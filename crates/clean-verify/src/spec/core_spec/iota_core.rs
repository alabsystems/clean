// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment E (#2859 computational-iota/delta track): the E-core assembly.
//!
//! `iota_reduct` is a 5-level nested `opt_bind` chain. `iota_reduct_some_inv` is
//! the CPS inverter: from `iota_reduct env e = some e'` it recovers the five
//! intermediate witnesses (recursor name, metadata, major premise, constructor
//! name, rule) together with each lookup equation and the reduct equation
//! `some REDUCT = some e'`, delivered to a continuation (the fragment has no
//! Sigma/Exists). Built by nesting `opt_bind_some_inv` five times, one per
//! `opt_bind` level. This is the decomposition the E-core commutation
//! (`iota_subst_commutes`) consumes to know `e` is a genuine redex with const
//! heads. See `designs/2026-06-14-computational-iota-delta-track.md` (Increment E).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_iota_core(&mut self) -> Result<(), SpecError> {
        // opt_bind_some_intro: the forward direction — if o = some w and f w =
        // some r then opt_bind o f = some r. The reconstruction half of E-core
        // rebuilds iota_reduct(inst e) = some (inst e') with this, one opt_bind
        // level at a time.
        self.add_definition(SpecDefinition {
            name: "opt_bind_some_intro".to_string(),
            type_src: concat!(
                "forall (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (w : a) (r : b), ",
                "Eq (OptionType a) o (OptionType.some a w) -> ",
                "Eq (OptionType b) (f w) (OptionType.some b r) -> ",
                "Eq (OptionType b) (opt_bind a b o f) (OptionType.some b r)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Type) (b : Type) (o : OptionType a) (f : a -> OptionType b) (w : a) (r : b) ",
                    "(ho : Eq (OptionType a) o (OptionType.some a w)) ",
                    "(hfw : Eq (OptionType b) (f w) (OptionType.some b r)) => ",
                    "Eq.trans (OptionType b) ",
                    "(opt_bind a b o f) (opt_bind a b (OptionType.some a w) f) (OptionType.some b r) ",
                    "(Eq.cong (OptionType a) (OptionType b) (fun (O : OptionType a) => opt_bind a b O f) ",
                    "o (OptionType.some a w) ho) ",
                    "(Eq.trans (OptionType b) ",
                    "(opt_bind a b (OptionType.some a w) f) (f w) (OptionType.some b r) ",
                    "(Eq.refl (OptionType b) (f w)) hfw)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "opt_bind forward intro: o = some w and f w = some r imply opt_bind o f = some r (opt_bind (some w) f reduces to f w). DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "opt_bind".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The arithmetic + reduct sub-terms of iota_reduct (verbatim from its def).
        let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
        let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
        let extras = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
        let fields =
            "(list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major))";
        let prefix = format!("(list_take {prefix_n} (kapp_args e))");
        let reduct = format!(
            "(apply_spine {extras} (apply_spine {fields} (apply_spine {prefix} (recrule_rhs rule))))"
        );

        // The opt_bind continuations L2..L6 (verbatim from iota_reduct, bottom-up).
        let l6 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct})");
        let l5 = format!(
            "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {l6})"
        );
        let l4 = format!(
            "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {l5})"
        );
        let l3 = format!("(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e))) {l4})");
        let l2 = format!(
            "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {l3})"
        );

        // The continuation type the inverter delivers to.
        let kont = format!(
            "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
             Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> \
             Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
             Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major) -> \
             Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
             Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
             Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
             C)"
        );

        let value = format!(
            "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Prop) \
             (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e')) \
             (k : {kont}) => \
             opt_bind_some_inv Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
             (fun (recname : Name) \
             (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
             (h1r : Eq (OptionType KExpr) ({l2} recname) (OptionType.some KExpr e')) => \
             opt_bind_some_inv RecMeta KExpr (recmeta_for env recname) {l3} e' C h1r \
             (fun (meta : RecMeta) \
             (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
             (h2r : Eq (OptionType KExpr) ({l3} meta) (OptionType.some KExpr e')) => \
             opt_bind_some_inv KExpr KExpr (list_head (list_drop {major_idx} (kapp_args e))) {l4} e' C h2r \
             (fun (major : KExpr) \
             (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
             (h3r : Eq (OptionType KExpr) ({l4} major) (OptionType.some KExpr e')) => \
             opt_bind_some_inv Name KExpr (kexpr_const_name (kapp_fn major)) {l5} e' C h3r \
             (fun (cname : Name) \
             (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
             (h4r : Eq (OptionType KExpr) ({l5} cname) (OptionType.some KExpr e')) => \
             opt_bind_some_inv RecRule KExpr (recrule_for env recname cname) {l6} e' C h4r \
             (fun (rule : RecRule) \
             (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
             (h5r : Eq (OptionType KExpr) ({l6} rule) (OptionType.some KExpr e')) => \
             k recname meta major cname rule h1 h2 h3 h4 h5 h5r))))))"
        );

        self.add_definition(SpecDefinition {
            name: "iota_reduct_some_inv".to_string(),
            type_src: format!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Prop), \
                 Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e') -> {kont} -> C"
            ),
            value_src: Some(value),
            is_axiom: false,
            description: concat!(
                "CPS inversion of iota_reduct's 5-level opt_bind chain: from iota_reduct env e = some e', ",
                "recover the recursor name, metadata, major premise, constructor name and rule with each ",
                "lookup equation and the reduct equation some REDUCT = some e', delivered to a continuation. ",
                "Five nested opt_bind_some_inv. The decomposition iota_subst_commutes consumes. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "opt_bind_some_inv".to_string(),
                "kexpr_const_name".to_string(),
                "recmeta_for".to_string(),
                "recrule_for".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // apply_spine3_inst: instantiate_at distributes through the three nested
        // apply_spine layers of the iota reduct (extras / fields / prefix), pushing
        // inst onto each arg list (list_map) and onto the rhs head. Three nested
        // instantiate_at_apply_spine. F := (fun a0 => instantiate_at a0 v d).
        let fmap = "(fun (a0 : KExpr) => instantiate_at a0 v d)";
        let final_term = format!(
            "(apply_spine (list_map {fmap} a) (apply_spine (list_map {fmap} b) (apply_spine (list_map {fmap} c) (instantiate_at rhs v d))))"
        );
        self.add_definition(SpecDefinition {
            name: "apply_spine3_inst".to_string(),
            type_src: format!(
                "forall (v : KExpr) (d : Nat) (a : ListType KExpr) (b : ListType KExpr) (c : ListType KExpr) (rhs : KExpr), \
                 Eq KExpr (instantiate_at (apply_spine a (apply_spine b (apply_spine c rhs))) v d) {final_term}"
            ),
            value_src: Some(format!(
                concat!(
                    "fun (v : KExpr) (d : Nat) (a : ListType KExpr) (b : ListType KExpr) (c : ListType KExpr) (rhs : KExpr) => ",
                    "Eq.trans KExpr ",
                    "(instantiate_at (apply_spine a (apply_spine b (apply_spine c rhs))) v d) ",
                    "(apply_spine (list_map {fmap} a) (instantiate_at (apply_spine b (apply_spine c rhs)) v d)) ",
                    "{final_term} ",
                    "(instantiate_at_apply_spine a (apply_spine b (apply_spine c rhs)) v d) ",
                    "(Eq.trans KExpr ",
                    "(apply_spine (list_map {fmap} a) (instantiate_at (apply_spine b (apply_spine c rhs)) v d)) ",
                    "(apply_spine (list_map {fmap} a) (apply_spine (list_map {fmap} b) (instantiate_at (apply_spine c rhs) v d))) ",
                    "{final_term} ",
                    "(Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine (list_map {fmap} a) Z) ",
                    "(instantiate_at (apply_spine b (apply_spine c rhs)) v d) ",
                    "(apply_spine (list_map {fmap} b) (instantiate_at (apply_spine c rhs) v d)) ",
                    "(instantiate_at_apply_spine b (apply_spine c rhs) v d)) ",
                    "(Eq.cong KExpr KExpr ",
                    "(fun (Z : KExpr) => apply_spine (list_map {fmap} a) (apply_spine (list_map {fmap} b) Z)) ",
                    "(instantiate_at (apply_spine c rhs) v d) ",
                    "(apply_spine (list_map {fmap} c) (instantiate_at rhs v d)) ",
                    "(instantiate_at_apply_spine c rhs v d)))"
                ),
                fmap = fmap,
                final_term = final_term,
            )),
            is_axiom: false,
            description: "instantiate_at distributes through the iota reduct's three nested apply_spine layers (pushing inst onto each arg list via list_map and onto the rhs head). Three nested instantiate_at_apply_spine. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "apply_spine".to_string(),
                "list_map".to_string(),
                "instantiate_at".to_string(),
                "instantiate_at_apply_spine".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_major_inst: the major premise survives instantiate_at — from the
        // head-const guard (h1) and list_head (list_drop kk (kapp_args e)) = some
        // major, conclude list_head (list_drop kk (kapp_args (inst e))) = some
        // (inst major). Chain: instantiate_at_kapp_args_const (h1) + list_map_drop +
        // list_map_head + opt_map_some. The level-3 reconstruction of E-core.
        let fmap2 = "(fun (a0 : KExpr) => instantiate_at a0 v d)";
        self.add_definition(SpecDefinition {
            name: "iota_major_inst".to_string(),
            type_src: concat!(
                "forall (v : KExpr) (d : Nat) (recname : Name) (e : KExpr) (kk : Nat) (major : KExpr), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> ",
                "Eq (OptionType KExpr) (list_head (list_drop kk (kapp_args e))) (OptionType.some KExpr major) -> ",
                "Eq (OptionType KExpr) (list_head (list_drop kk (kapp_args (instantiate_at e v d)))) (OptionType.some KExpr (instantiate_at major v d))"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (v : KExpr) (d : Nat) (recname : Name) (e : KExpr) (kk : Nat) (major : KExpr) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) ",
                    "(h3 : Eq (OptionType KExpr) (list_head (list_drop kk (kapp_args e))) (OptionType.some KExpr major)) => ",
                    "Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop kk (kapp_args (instantiate_at e v d)))) ",
                    "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                    "(OptionType.some KExpr (instantiate_at major v d)) ",
                    // LHS -> opt_map F (list_head (list_drop kk (kapp_args e)))
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop kk (kapp_args (instantiate_at e v d)))) ",
                    "(list_head (list_drop kk (list_map {f} (kapp_args e)))) ",
                    "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop kk L)) ",
                    "(kapp_args (instantiate_at e v d)) (list_map {f} (kapp_args e)) ",
                    "(instantiate_at_kapp_args_const v d recname e h1)) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop kk (list_map {f} (kapp_args e)))) ",
                    "(list_head (list_map {f} (list_drop kk (kapp_args e)))) ",
                    "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_drop kk (list_map {f} (kapp_args e))) (list_map {f} (list_drop kk (kapp_args e))) ",
                    "(list_map_drop {f} kk (kapp_args e))) ",
                    "(list_map_head {f} (list_drop kk (kapp_args e))))) ",
                    // opt_map F (...) -> some (inst major)
                    "(Eq.trans (OptionType KExpr) ",
                    "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                    "(opt_map {f} (OptionType.some KExpr major)) ",
                    "(OptionType.some KExpr (instantiate_at major v d)) ",
                    "(Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (O : OptionType KExpr) => opt_map {f} O) ",
                    "(list_head (list_drop kk (kapp_args e))) (OptionType.some KExpr major) h3) ",
                    "(opt_map_some {f} major))"
                ),
                f = fmap2,
            )),
            is_axiom: false,
            description: "The iota major premise survives instantiate_at (up to inst): under the head-const guard, list_head (list_drop kk (kapp_args (inst e))) = some (inst major). Chain via instantiate_at_kapp_args_const + list_map_drop + list_map_head + opt_map_some. The level-3 reconstruction of E-core. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "list_drop".to_string(),
                "list_head".to_string(),
                "opt_map".to_string(),
                "instantiate_at".to_string(),
                "instantiate_at_kapp_args_const".to_string(),
                "list_map_drop".to_string(),
                "list_map_head".to_string(),
                "opt_map_some".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The three list-segment rewrites of the reduct (extras = list_drop,
        // prefix = list_take on kapp_args e; fields = list_drop on kapp_args major
        // with a list_length-derived offset). Each: kapp_args commutes with inst
        // (const-head guard) + the list_map/list op commutes.
        let f3 = "(fun (a0 : KExpr) => instantiate_at a0 v d)";

        // kapp_drop_inst: list_drop kk (kapp_args (inst e)) = list_map F (list_drop kk (kapp_args e)).
        self.add_definition(SpecDefinition {
            name: "kapp_drop_inst".to_string(),
            type_src: concat!(
                "forall (v : KExpr) (d : Nat) (recname : Name) (e : KExpr) (kk : Nat), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> ",
                "Eq (ListType KExpr) (list_drop kk (kapp_args (instantiate_at e v d))) ",
                "(list_map (fun (a0 : KExpr) => instantiate_at a0 v d) (list_drop kk (kapp_args e)))"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (v : KExpr) (d : Nat) (recname : Name) (e : KExpr) (kk : Nat) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_drop kk (kapp_args (instantiate_at e v d))) ",
                    "(list_drop kk (list_map {f} (kapp_args e))) ",
                    "(list_map {f} (list_drop kk (kapp_args e))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop kk L) ",
                    "(kapp_args (instantiate_at e v d)) (list_map {f} (kapp_args e)) ",
                    "(instantiate_at_kapp_args_const v d recname e h1)) ",
                    "(list_map_drop {f} kk (kapp_args e))"
                ),
                f = f3,
            )),
            is_axiom: false,
            description: "list_drop kk (kapp_args (inst e)) = list_map (inst .) (list_drop kk (kapp_args e)) under the head-const guard. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "list_drop".to_string(),
                "list_map".to_string(),
                "instantiate_at_kapp_args_const".to_string(),
                "list_map_drop".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_take_inst: list_take pn (kapp_args (inst e)) = list_map F (list_take pn (kapp_args e)).
        self.add_definition(SpecDefinition {
            name: "kapp_take_inst".to_string(),
            type_src: concat!(
                "forall (v : KExpr) (d : Nat) (recname : Name) (e : KExpr) (pn : Nat), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> ",
                "Eq (ListType KExpr) (list_take pn (kapp_args (instantiate_at e v d))) ",
                "(list_map (fun (a0 : KExpr) => instantiate_at a0 v d) (list_take pn (kapp_args e)))"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (v : KExpr) (d : Nat) (recname : Name) (e : KExpr) (pn : Nat) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_take pn (kapp_args (instantiate_at e v d))) ",
                    "(list_take pn (list_map {f} (kapp_args e))) ",
                    "(list_map {f} (list_take pn (kapp_args e))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_take pn L) ",
                    "(kapp_args (instantiate_at e v d)) (list_map {f} (kapp_args e)) ",
                    "(instantiate_at_kapp_args_const v d recname e h1)) ",
                    "(list_map_take {f} pn (kapp_args e))"
                ),
                f = f3,
            )),
            is_axiom: false,
            description: "list_take pn (kapp_args (inst e)) = list_map (inst .) (list_take pn (kapp_args e)) under the head-const guard. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "list_take".to_string(),
                "list_map".to_string(),
                "instantiate_at_kapp_args_const".to_string(),
                "list_map_take".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_drop_cong: congruence of list_drop in its OFFSET (first, Nat) arg.
        //
        // Proved by `Eq.subst` with a Prop motive. We CANNOT use the natural
        // `Eq.cong Nat (ListType KExpr) (fun q => list_drop q xs) m n h` here:
        // the elaborator's structural unifier rejects `Eq.cong` in the
        // (Const α = Nat, App β = ListType KExpr) direction (it falls into the
        // kernel-def-eq fallback and reports "expected Const(Nat), got App vs
        // Const"). The (App, App) / (App, Const) / (Const, Const) directions
        // used elsewhere in this file are fine; only (Const, App) trips it.
        // `Eq.subst` (motive : Nat -> Prop, since `Eq … : Prop`) sidesteps the
        // bad direction entirely and is the load-bearing offset-rewrite for the
        // fields segment, whose offset (`list_length (kapp_args major) - nf`) is
        // only PROPOSITIONALLY equal across `instantiate_at` (via list_map_length).
        self.add_definition(SpecDefinition {
            name: "list_drop_cong".to_string(),
            type_src: concat!(
                "forall (m : Nat) (n : Nat) (xs : ListType KExpr), ",
                "Eq Nat m n -> Eq (ListType KExpr) (list_drop m xs) (list_drop n xs)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (m : Nat) (n : Nat) (xs : ListType KExpr) (h : Eq Nat m n) => ",
                    "Eq.subst Nat ",
                    "(fun (k : Nat) => Eq (ListType KExpr) (list_drop m xs) (list_drop k xs)) ",
                    "m n h ",
                    "(Eq.refl (ListType KExpr) (list_drop m xs))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Congruence of list_drop in its Nat offset: m = n -> list_drop m xs = list_drop n xs. Proved by Eq.subst (Prop motive) — the Eq.cong (Const,App) direction is rejected by the elaborator's unifier. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_drop".to_string(),
                "Eq.subst".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_fields_inst: the fields segment survives inst:
        //   list_drop off_i KA_AM = list_map F (list_drop off KA_M)
        // where KA_AM = kapp_args (inst major), KA_M = kapp_args major,
        //   F = (fun a0 => instantiate_at a0 v d), MAP_KA_M = list_map F KA_M,
        //   off_i = Nat.sub (list_length KA_AM) nf, off = Nat.sub (list_length KA_M) nf,
        //   off_mid = Nat.sub (list_length MAP_KA_M) nf.
        // Chain: list_drop off_i KA_AM
        //   =[s_off : list_drop_cong, offset off_i -> off]   list_drop off KA_AM
        //   =[s_list: Eq.cong list, KA_AM -> MAP_KA_M]        list_drop off MAP_KA_M
        //   =[s2   : list_map_drop]                           list_map F (list_drop off KA_M).
        // The offset equality eoff : off_i = off goes via off_mid:
        //   eoff1 (KA_AM -> MAP_KA_M inside list_length) ∘ eoff2 (list_map_length).
        let fields_off = "(Nat.sub (list_length (kapp_args major)) nf)";
        let fields_off_inst = "(Nat.sub (list_length (kapp_args (instantiate_at major v d))) nf)";
        let fields_off_mid = "(Nat.sub (list_length (list_map (fun (a0 : KExpr) => instantiate_at a0 v d) (kapp_args major))) nf)";
        self.add_definition(SpecDefinition {
            name: "kapp_fields_inst".to_string(),
            type_src: format!(
                concat!(
                    "forall (v : KExpr) (d : Nat) (cname : Name) (major : KExpr) (nf : Nat), ",
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> ",
                    "Eq (ListType KExpr) (list_drop {off_i} (kapp_args (instantiate_at major v d))) ",
                    "(list_map (fun (a0 : KExpr) => instantiate_at a0 v d) (list_drop {off} (kapp_args major)))"
                ),
                off_i = fields_off_inst,
                off = fields_off,
            ),
            value_src: Some(format!(
                concat!(
                    "fun (v : KExpr) (d : Nat) (cname : Name) (major : KExpr) (nf : Nat) ",
                    "(h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) => ",
                    // result = s1 ∘ s2, s1 = s_off ∘ s_list.
                    "Eq.trans (ListType KExpr) ",
                    "(list_drop {off_i} (kapp_args (instantiate_at major v d))) ",
                    "(list_drop {off} (list_map {f} (kapp_args major))) ",
                    "(list_map {f} (list_drop {off} (kapp_args major))) ",
                    // s1 = s_off ∘ s_list
                    "(Eq.trans (ListType KExpr) ",
                    "(list_drop {off_i} (kapp_args (instantiate_at major v d))) ",
                    "(list_drop {off} (kapp_args (instantiate_at major v d))) ",
                    "(list_drop {off} (list_map {f} (kapp_args major))) ",
                    // s_off: rewrite offset off_i -> off (list fixed at KA_AM), via list_drop_cong.
                    "(list_drop_cong {off_i} {off} (kapp_args (instantiate_at major v d)) ",
                    // eoff : off_i = off  =  eoff1 ∘ eoff2
                    "(Eq.trans Nat {off_i} {off_mid} {off} ",
                    // eoff1: KA_AM -> MAP_KA_M inside list_length (App α, Const β — OK).
                    "(Eq.cong (ListType KExpr) Nat ",
                    "(fun (L : ListType KExpr) => Nat.sub (list_length L) nf) ",
                    "(kapp_args (instantiate_at major v d)) (list_map {f} (kapp_args major)) ",
                    "(instantiate_at_kapp_args_const v d cname major h4)) ",
                    // eoff2: collapse list_length (list_map F ..) -> list_length .. (Const, Const — OK).
                    "(Eq.cong Nat Nat (fun (q : Nat) => Nat.sub q nf) ",
                    "(list_length (list_map {f} (kapp_args major))) (list_length (kapp_args major)) ",
                    "(list_map_length {f} (kapp_args major))))) ",
                    // s_list: rewrite list KA_AM -> MAP_KA_M (offset fixed at off; App, App — OK).
                    "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                    "(fun (L : ListType KExpr) => list_drop {off} L) ",
                    "(kapp_args (instantiate_at major v d)) (list_map {f} (kapp_args major)) ",
                    "(instantiate_at_kapp_args_const v d cname major h4))) ",
                    // s2: list_drop off (list_map F ..) = list_map F (list_drop off ..)
                    "(list_map_drop {f} {off} (kapp_args major))"
                ),
                f = f3,
                off = fields_off,
                off_i = fields_off_inst,
                off_mid = fields_off_mid,
            )),
            is_axiom: false,
            description: "The fields segment survives inst: list_drop (offset on inst major) (kapp_args (inst major)) = list_map (inst .) (list_drop (offset on major) (kapp_args major)). The offset (list_length (kapp_args major) - nf) is preserved by list_map_length; the offset rewrite uses list_drop_cong (Eq.subst). Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "list_drop".to_string(),
                "list_length".to_string(),
                "list_map".to_string(),
                "instantiate_at_kapp_args_const".to_string(),
                "list_map_length".to_string(),
                "list_map_drop".to_string(),
                "list_drop_cong".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // iota_reduct_inst_eq: the REDUCT EQUATION — the spine algebra of E-core.
        // Given the redex witnesses (head-const guards h1 on e, h4 on major; rule
        // lookup h5; the original reduct equation h5r : some REDUCT = some e') and a
        // CLOSED env, the reduct recomputed on the inst side equals inst of the
        // original reduct, which equals inst e':
        //   REDUCT_i = inst REDUCT = inst e'.
        // REDUCT = apply_spine ext (apply_spine fld (apply_spine pre rhs)) with
        //   ext = list_drop (succ major_idx) (kapp_args e)  [extras]
        //   fld = list_drop (len(kapp_args major) - nf) (kapp_args major)  [fields]
        //   pre = list_take prefix_n (kapp_args e)  [prefix], rhs = recrule_rhs rule.
        // Each segment survives inst: ext_i = map F ext (kapp_drop_inst, h1),
        // pre_i = map F pre (kapp_take_inst, h1), fld_i = map F fld
        // (kapp_fields_inst, h4); the rhs slot stays bare and equals inst rhs only
        // because the env is closed (recenv_closed_rhs, h5); apply_spine3_inst pushes
        // inst through the three apply_spine layers; option_some_inj on h5r gives
        // REDUCT = e'.
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            let fmap = "(fun (a0 : KExpr) => instantiate_at a0 v d)";

            // original-side segments (on e / major)
            let ext = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
            let fld = format!(
                "(list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major))"
            );
            let pre = format!("(list_take {prefix_n} (kapp_args e))");
            let reduct =
                format!("(apply_spine {ext} (apply_spine {fld} (apply_spine {pre} {p_rhs})))");

            // inst-side segments (on inst e / inst major); rhs slot stays bare.
            let ext_i =
                format!("(list_drop (Nat.succ {major_idx}) (kapp_args (instantiate_at e v d)))");
            let fld_i = format!("(list_drop (Nat.sub (list_length (kapp_args (instantiate_at major v d))) {nf}) (kapp_args (instantiate_at major v d)))");
            let pre_i = format!("(list_take {prefix_n} (kapp_args (instantiate_at e v d)))");
            let reduct_i = format!(
                "(apply_spine {ext_i} (apply_spine {fld_i} (apply_spine {pre_i} {p_rhs})))"
            );

            // map-F versions + inst rhs + inst REDUCT.
            let mext = format!("(list_map {fmap} {ext})");
            let mfld = format!("(list_map {fmap} {fld})");
            let mpre = format!("(list_map {fmap} {pre})");
            let i_rhs = format!("(instantiate_at {p_rhs} v d)");
            let reduct_unfolded =
                format!("(apply_spine {mext} (apply_spine {mfld} (apply_spine {mpre} {i_rhs})))");
            let inst_reduct = format!("(instantiate_at {reduct} v d)");

            // inner: apply_spine pre_i rhs = apply_spine (map F pre) (inst rhs).
            let inner = format!(
                "(Eq.trans KExpr \
                 (apply_spine {pre_i} {p_rhs}) (apply_spine {mpre} {p_rhs}) (apply_spine {mpre} {i_rhs}) \
                 (Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L {p_rhs}) \
                 {pre_i} {mpre} (kapp_take_inst v d recname e {prefix_n} h1)) \
                 (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine {mpre} Z) \
                 {p_rhs} {i_rhs} \
                 (Eq.symm KExpr {i_rhs} {p_rhs} (recenv_closed_rhs env recname cname rule v d closed h5))))"
            );

            // middle: apply_spine fld_i (apply_spine pre_i rhs)
            //       = apply_spine (map F fld) (apply_spine (map F pre) (inst rhs)).
            let middle = format!(
                "(Eq.trans KExpr \
                 (apply_spine {fld_i} (apply_spine {pre_i} {p_rhs})) \
                 (apply_spine {mfld} (apply_spine {pre_i} {p_rhs})) \
                 (apply_spine {mfld} (apply_spine {mpre} {i_rhs})) \
                 (Eq.cong (ListType KExpr) KExpr \
                 (fun (L : ListType KExpr) => apply_spine L (apply_spine {pre_i} {p_rhs})) \
                 {fld_i} {mfld} (kapp_fields_inst v d cname major {nf} h4)) \
                 (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine {mfld} Z) \
                 (apply_spine {pre_i} {p_rhs}) (apply_spine {mpre} {i_rhs}) {inner}))"
            );

            // outer: REDUCT_i = apply_spine (map F ext) (apply_spine (map F fld) (apply_spine (map F pre) (inst rhs))).
            let outer = format!(
                "(Eq.trans KExpr \
                 {reduct_i} \
                 (apply_spine {mext} (apply_spine {fld_i} (apply_spine {pre_i} {p_rhs}))) \
                 {reduct_unfolded} \
                 (Eq.cong (ListType KExpr) KExpr \
                 (fun (L : ListType KExpr) => apply_spine L (apply_spine {fld_i} (apply_spine {pre_i} {p_rhs}))) \
                 {ext_i} {mext} (kapp_drop_inst v d recname e (Nat.succ {major_idx}) h1)) \
                 (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine {mext} Z) \
                 (apply_spine {fld_i} (apply_spine {pre_i} {p_rhs})) \
                 (apply_spine {mfld} (apply_spine {mpre} {i_rhs})) {middle}))"
            );

            // spine_eq: REDUCT_i = inst REDUCT (outer ∘ symm apply_spine3_inst).
            let spine_eq = format!(
                "(Eq.trans KExpr {reduct_i} {reduct_unfolded} {inst_reduct} {outer} \
                 (Eq.symm KExpr {inst_reduct} {reduct_unfolded} \
                 (apply_spine3_inst v d {ext} {fld} {pre} {p_rhs})))"
            );

            // inst_eq: inst REDUCT = inst e' (cong inst on option_some_inj h5r).
            let inst_eq = format!(
                "(Eq.cong KExpr KExpr {fmap} {reduct} e' (option_some_inj KExpr {reduct} e' h5r))"
            );

            let value = format!(
                "fun (env : RecEnv) (v : KExpr) (d : Nat) (e : KExpr) (e' : KExpr) \
                 (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (closed : RecEnvClosed env) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e')) => \
                 Eq.trans KExpr {reduct_i} {inst_reduct} (instantiate_at e' v d) {spine_eq} {inst_eq}"
            );

            let type_src = format!(
                "forall (env : RecEnv) (v : KExpr) (d : Nat) (e : KExpr) (e' : KExpr) \
                 (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                 RecEnvClosed env -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
                 Eq KExpr {reduct_i} (instantiate_at e' v d)"
            );

            self.add_definition(SpecDefinition {
                name: "iota_reduct_inst_eq".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "The reduct equation of E-core: under a closed env and the redex head-const guards, the iota reduct recomputed on the inst side equals inst of the original reduct (= inst e'). Composes kapp_drop/take/fields_inst (segment survival) + recenv_closed_rhs (rhs slot) + apply_spine3_inst (inst through apply_spine) + option_some_inj (REDUCT = e'). The single largest proof term in the track. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kapp_args".to_string(),
                    "apply_spine".to_string(),
                    "list_map".to_string(),
                    "list_drop".to_string(),
                    "list_take".to_string(),
                    "recrule_rhs".to_string(),
                    "recrule_num_fields".to_string(),
                    "kapp_drop_inst".to_string(),
                    "kapp_take_inst".to_string(),
                    "kapp_fields_inst".to_string(),
                    "apply_spine3_inst".to_string(),
                    "recenv_closed_rhs".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_subst_commutes: THE E-core result. instantiate_at commutes past the
        // directed iota step (iota_step = graph of iota_reduct):
        //   RecEnvClosed env -> iota_reduct env e = some e'
        //     -> iota_reduct env (inst e) = some (inst e').
        // Inverts the LHS via iota_reduct_some_inv (recovering the 5 redex
        // witnesses + lookups + the reduct equation), then reconstructs the
        // inst-side reduct via opt_bind_some_intro 5×: the head-const lookups
        // survive inst (kexpr_const_name_instantiate_const, levels 1 & 4), the
        // major premise survives (iota_major_inst, level 3), the metadata/rule
        // lookups are unchanged (h2, h5), and the reduct slot is closed by
        // iota_reduct_inst_eq (level 6). The const-head rigidity is what makes the
        // kapp_fn-vs-inst non-commutation never bite.
        {
            let ei = "(instantiate_at e v d)";
            let im = "(instantiate_at major v d)";
            let iep = "(instantiate_at e' v d)";
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";

            // The reduct, parameterized by the e-expr and major-expr (mirrors
            // iota_reduct's def + iota_reduct_some_inv exactly).
            let mk_reduct = |es: &str, ms: &str| -> String {
                format!(
                    "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args {es})) \
                     (apply_spine (list_drop (Nat.sub (list_length (kapp_args {ms})) (recrule_num_fields rule)) (kapp_args {ms})) \
                     (apply_spine (list_take {prefix_n} (kapp_args {es})) (recrule_rhs rule))))"
                )
            };
            let reduct_orig = mk_reduct("e", "major");
            let reduct_i_majvar = mk_reduct(ei, "major");
            let reduct_i_majinst = mk_reduct(ei, im);

            // The inst-side opt_bind continuations (iota_reduct's def with e:=inst e;
            // f4sub/f5sub carry major:=inst major for the level-4/5 obligations).
            let f5 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct_i_majvar})");
            let f4 = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {f5})"
            );
            let f3 = format!(
                "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {f4})"
            );
            let f2 = format!(
                "(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args {ei}))) {f3})"
            );
            let f1 = format!(
                "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {f2})"
            );
            let f5sub =
                format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct_i_majinst})");
            let f4sub = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {f5sub})"
            );

            // Inst-side lookups: heads survive inst (levels 1 & 4); major survives (3).
            let h1i = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {ei})) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) \
                 (kexpr_const_name_instantiate_const v d recname e h1) h1)"
            );
            let h3i = format!("(iota_major_inst v d recname e {major_idx} major h1 h3)");
            let h4i = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {im})) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) \
                 (kexpr_const_name_instantiate_const v d cname major h4) h4)"
            );
            // Level-6: some REDUCT_i = some (inst e') via iota_reduct_inst_eq + cong.
            let hf6 = format!(
                "(Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr X) \
                 {reduct_i_majinst} {iep} \
                 (iota_reduct_inst_eq env v d e e' recname meta major cname rule closed h1 h4 h5 h5r))"
            );

            // The nested opt_bind_some_intro chain (outside-in, 5 levels).
            let recon = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {ei})) {f1} recname {iep} {h1i} \
                 (opt_bind_some_intro RecMeta KExpr (recmeta_for env recname) {f2} meta {iep} h2 \
                 (opt_bind_some_intro KExpr KExpr (list_head (list_drop {major_idx} (kapp_args {ei}))) {f3} {im} {iep} {h3i} \
                 (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {im})) {f4sub} cname {iep} {h4i} \
                 (opt_bind_some_intro RecRule KExpr (recrule_for env recname cname) {f5sub} rule {iep} h5 {hf6}))))"
            );

            // The continuation k passed to iota_reduct_some_inv (binders match kont).
            let kont_lambda = format!(
                "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_orig}) (OptionType.some KExpr e')) => \
                 {recon})"
            );

            let goal_c = format!(
                "(Eq (OptionType KExpr) (iota_reduct env {ei}) (OptionType.some KExpr {iep}))"
            );

            let value = format!(
                "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat) \
                 (closed : RecEnvClosed env) \
                 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e')) => \
                 iota_reduct_some_inv env e e' {goal_c} h {kont_lambda}"
            );

            self.add_definition(SpecDefinition {
                name: "iota_subst_commutes".to_string(),
                type_src: concat!(
                    "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (v : KExpr) (d : Nat), ",
                    "RecEnvClosed env -> ",
                    "Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e') -> ",
                    "Eq (OptionType KExpr) (iota_reduct env (instantiate_at e v d)) (OptionType.some KExpr (instantiate_at e' v d))"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "E-core result: instantiate_at commutes past the directed iota step. From a closed env and iota_reduct env e = some e', derive iota_reduct env (inst e) = some (inst e'). Inverts via iota_reduct_some_inv then reconstructs via opt_bind_some_intro 5× (const-head lookups survive inst, major survives, metadata/rule unchanged, reduct slot closed by iota_reduct_inst_eq). The par_subst iota arm consumes this. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "iota_reduct_inst_eq".to_string(),
                    "iota_major_inst".to_string(),
                    "kexpr_const_name_instantiate_const".to_string(),
                    "recenv_closed_rhs".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_step_head_none_absurd: a genuine iota redex is CONST-headed. If the
        // head const-name is `none` (a non-const head — lam/pi/sort/bvar after
        // kapp_fn) then iota_step is impossible: invert via iota_reduct_some_inv to
        // recover h1 (the head IS some recname), contradict via option_none_ne_some.
        // The discharge primitive the par_strips_c iota-source case uses to kill the
        // beta/lam/pi/forall_/let_ arms (their kapp_fn head is a binder ⇒ none).
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let reduct = format!(
                "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args e)) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) \
                 (apply_spine (list_take {prefix_n} (kapp_args e)) (recrule_rhs rule))))"
            );
            let value = format!(
                "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Prop) \
                 (hnone : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name)) \
                 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e')) => \
                 iota_reduct_some_inv env e e' C h \
                 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e')) => \
                 option_none_ne_some Name recname C \
                 (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) \
                 (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) hnone) h1))"
            );
            self.add_definition(SpecDefinition {
                name: "iota_step_head_none_absurd".to_string(),
                type_src: concat!(
                    "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (C : Prop), ",
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) -> ",
                    "iota_step env e e' -> C"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "A genuine iota redex is const-headed: if kexpr_const_name (kapp_fn e) = none then iota_step env e e' is impossible. Inverts via iota_reduct_some_inv (recovering h1: the head IS some recname) and contradicts the none-head hypothesis via option_none_ne_some. The discharge primitive for the beta/lam/pi/forall_/let_ arms of the par_strips_c iota-source case (their kapp_fn is a binder ⇒ none). DerivedProved, zero axiom_deps. Part of #2859 (Increment F).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct_some_inv".to_string(),
                    "option_none_ne_some".to_string(),
                    "kexpr_const_name".to_string(),
                    "kapp_fn".to_string(),
                    "iota_step".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // =====================================================================
        // Over-application substrate (#2859 (iota,app) confluence): the list
        // segment facts the over-applied iota redex needs. When a recursor
        // application is OVER-applied (more args than the rule consumes), the
        // appended extra arg lives strictly past the major-premise window, so
        // drop/take/head over the spine are unaffected by it.
        // =====================================================================

        // 1. list_drop_append_ge: if n <= length xs then dropping n from
        // (xs ++ [a]) is (drop n xs) ++ [a] — the appended tail survives the drop
        // because the drop count is within xs. Induction: Le.rec collapses to
        // Nat.sub n (length xs) = 0, then Nat.rec on n with the motive
        // generalizing xs; the succ case-splits xs (ListType.rec). The nil/succ
        // corner is absurd (Le (succ m) 0) and discharged via Empty.rec on a
        // reduced discriminator. List ops never auto-reduce through the spec
        // recursors, so each step inserts the explicit unfold lemma.
        {
            // Discriminator: D z = Nat for z = succ _, Empty for z = zero.
            let discr = "(Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat))";
            // From h_nil : Nat.sub (succ m) (list_length nil) = 0 derive succ m = 0.
            let succ_eq_zero = concat!(
                "(Eq.trans Nat (Nat.succ m) (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) Nat.zero ",
                // succ m = Nat.sub (succ m) (list_length nil)
                "(Eq.symm Nat (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) (Nat.succ m) ",
                "(Eq.trans Nat (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) (Nat.sub (Nat.succ m) Nat.zero) (Nat.succ m) ",
                "(Eq.cong Nat Nat (fun (y : Nat) => Nat.sub (Nat.succ m) y) (list_length (ListType.nil KExpr)) Nat.zero (list_length_nil)) ",
                "(nat_sub_zero_right (Nat.succ m)))) ",
                "h_nil)"
            );
            let nil_absurd = format!(
                concat!(
                    "(fun (h_nil : Eq Nat (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) Nat.zero) => ",
                    "Empty.rec (fun (_ : Empty) => Eq (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (list_append (ListType.nil KExpr) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_append (list_drop (Nat.succ m) (ListType.nil KExpr)) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(Eq.substType Nat {discr} (Nat.succ m) Nat.zero {succ_eq_zero} (Nat.succ m)))"
                ),
                discr = discr,
                succ_eq_zero = succ_eq_zero,
            );

            // cons case of the succ arm. h_cons : Nat.sub (succ m) (length (x::rest)) = 0.
            // Want: drop (succ m) ((x::rest) ++ [a]) = (drop (succ m) (x::rest)) ++ [a].
            // LHS: (x::rest)++[a] = x::(rest++[a]); drop (succ m) (x::L) = drop m (tail (x::L)) = drop m (rest++[a]).
            // Then ih rest (with Nat.sub m (length rest) = 0) gives drop m (rest++[a]) = (drop m rest)++[a].
            // RHS: drop (succ m) (x::rest) = drop m rest, so (drop m rest)++[a] = RHS.
            let cons_case = concat!(
                "(fun (x : KExpr) (rest : ListType KExpr) ",
                "(_ihinner : Eq Nat (Nat.sub (Nat.succ m) (list_length rest)) Nat.zero -> ",
                "Eq (ListType KExpr) (list_drop (Nat.succ m) (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_append (list_drop (Nat.succ m) rest) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(h_cons : Eq Nat (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) Nat.zero) => ",
                // sub_m_rest : Nat.sub m (length rest) = 0, from h_cons.
                // h_cons : Nat.sub (succ m) (length (x::rest)) = 0
                //   = Nat.sub (succ m) (succ (length rest))  [list_length_cons]
                //   = Nat.sub m (length rest)                [nat_sub_succ_succ]
                "(fun (sub_m_rest : Eq Nat (Nat.sub m (list_length rest)) Nat.zero) => ",
                "Eq.trans (ListType KExpr) ",
                "(list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_drop m (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_append (list_drop (Nat.succ m) (ListType.cons KExpr x rest)) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                // LEG A: LHS = drop m (rest ++ [a])
                "(Eq.trans (ListType KExpr) ",
                "(list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))) ",
                "(list_drop m (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                // append cons: (x::rest)++[a] = x::(rest++[a])
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop (Nat.succ m) L) ",
                "(list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_append_cons x rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                // drop (succ m) (x::L) = drop m (tail (x::L)) = drop m L
                "(Eq.trans (ListType KExpr) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))) ",
                "(list_drop m (list_tail (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))))) ",
                "(list_drop m (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_drop_succ m (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                "(list_tail (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))) ",
                "(list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_tail_cons x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))))) ",
                // LEG B: drop m (rest ++ [a]) = (drop (succ m) (x::rest)) ++ [a]
                "(Eq.trans (ListType KExpr) ",
                "(list_drop m (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_append (list_drop m rest) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_append (list_drop (Nat.succ m) (ListType.cons KExpr x rest)) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                // ih rest sub_m_rest
                "(ih rest sub_m_rest) ",
                // (drop m rest)++[a] = (drop (succ m) (x::rest))++[a]  (since drop (succ m)(x::rest)=drop m rest)
                "(Eq.symm (ListType KExpr) ",
                "(list_append (list_drop (Nat.succ m) (ListType.cons KExpr x rest)) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_append (list_drop m rest) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_append L (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x rest)) (list_drop m rest) ",
                "(Eq.trans (ListType KExpr) (list_drop (Nat.succ m) (ListType.cons KExpr x rest)) ",
                "(list_drop m (list_tail (ListType.cons KExpr x rest))) (list_drop m rest) ",
                "(list_drop_succ m (ListType.cons KExpr x rest)) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                "(list_tail (ListType.cons KExpr x rest)) rest (list_tail_cons x rest))))))) ",
                // close the sub_m_rest binder by applying it to the derived equation
                "(Eq.trans Nat (Nat.sub m (list_length rest)) (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) Nat.zero ",
                "(Eq.symm Nat (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) (Nat.sub m (list_length rest)) ",
                "(Eq.trans Nat (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) (Nat.sub (Nat.succ m) (Nat.succ (list_length rest))) (Nat.sub m (list_length rest)) ",
                "(Eq.cong Nat Nat (fun (y : Nat) => Nat.sub (Nat.succ m) y) (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) (list_length_cons x rest)) ",
                "(nat_sub_succ_succ m (list_length rest)))) ",
                "h_cons))"
            );

            // succ arm body: ListType.rec on xs0 with motive carrying h.
            let succ_arm = format!(
                concat!(
                    "(fun (m : Nat) ",
                    "(ih : forall (xs0 : ListType KExpr), Eq Nat (Nat.sub m (list_length xs0)) Nat.zero -> ",
                    "Eq (ListType KExpr) (list_drop m (list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_append (list_drop m xs0) (ListType.cons KExpr a0 (ListType.nil KExpr)))) => ",
                    "fun (xs0 : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq Nat (Nat.sub (Nat.succ m) (list_length xs1)) Nat.zero -> ",
                    "Eq (ListType KExpr) (list_drop (Nat.succ m) (list_append xs1 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_append (list_drop (Nat.succ m) xs1) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "{nil_absurd} ",
                    "{cons_case} ",
                    "xs0)"
                ),
                nil_absurd = nil_absurd,
                cons_case = cons_case,
            );

            // zero arm: drop 0 (xs ++ [a]) = xs ++ [a] = (drop 0 xs) ++ [a].
            let zero_arm = concat!(
                "(fun (xs0 : ListType KExpr) (_h0 : Eq Nat (Nat.sub Nat.zero (list_length xs0)) Nat.zero) => ",
                "Eq.trans (ListType KExpr) ",
                "(list_drop Nat.zero (list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_append (list_drop Nat.zero xs0) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_drop_zero (list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(Eq.symm (ListType KExpr) ",
                "(list_append (list_drop Nat.zero xs0) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_append L (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(list_drop Nat.zero xs0) xs0 (list_drop_zero xs0))))"
            );

            // Le.rec collapse: Le n (length xs) -> Nat.sub n (length xs) = 0.
            // The first index n of Le is FIXED (preserved across both ctors), so
            // the elaborator promotes it to a PARAMETER: Le.rec n motive refl step
            // (second index) major. Motive ranges only over the second index j.
            let le_to_sub = concat!(
                "(Le.rec n (fun (j : Nat) (_ : Le n j) => Eq Nat (Nat.sub n j) Nat.zero) ",
                "(nat_sub_self n) ",
                "(fun (m : Nat) (_h : Le n m) (ihm : Eq Nat (Nat.sub n m) Nat.zero) => ",
                // Nat.sub n (succ m) = pred (Nat.sub n m) = pred 0 = 0
                "Eq.trans Nat (Nat.sub n (Nat.succ m)) (Nat.pred (Nat.sub n m)) Nat.zero ",
                "(Eq.refl Nat (Nat.pred (Nat.sub n m))) ",
                "(Eq.trans Nat (Nat.pred (Nat.sub n m)) (Nat.pred Nat.zero) Nat.zero ",
                "(Eq.cong Nat Nat Nat.pred (Nat.sub n m) Nat.zero ihm) (Eq.refl Nat Nat.zero))) ",
                "(list_length xs) hle)"
            );

            let value = format!(
                concat!(
                    "fun (n : Nat) (xs : ListType KExpr) (a : KExpr) (hle : Le n (list_length xs)) => ",
                    "(fun (hsub : Eq Nat (Nat.sub n (list_length xs)) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (xs0 : ListType KExpr), Eq Nat (Nat.sub n0 (list_length xs0)) Nat.zero -> ",
                    "Eq (ListType KExpr) (list_drop n0 (list_append xs0 (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                    "(list_append (list_drop n0 xs0) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                    "{zero_arm} ",
                    "{succ_arm} ",
                    "n xs hsub) ",
                    "{le_to_sub}"
                ),
                zero_arm = zero_arm.replace("a0", "a"),
                succ_arm = succ_arm.replace("a0", "a"),
                le_to_sub = le_to_sub,
            );

            self.add_definition(SpecDefinition {
                name: "list_drop_append_ge".to_string(),
                type_src: concat!(
                    "forall (n : Nat) (xs : ListType KExpr) (a : KExpr), ",
                    "Le n (list_length xs) -> ",
                    "Eq (ListType KExpr) (list_drop n (list_append xs (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                    "(list_append (list_drop n xs) (ListType.cons KExpr a (ListType.nil KExpr)))"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "If n <= length xs then list_drop n (xs ++ [a]) = (list_drop n xs) ++ [a]: the appended tail survives a drop within xs. Le.rec collapses to Nat.sub n (length xs) = 0, then Nat.rec on n / ListType.rec on xs; the absurd nil/succ corner discharged via Empty.rec on a reduced discriminator. DerivedProved, zero axiom_deps. Part of #2859 (iota,app over-application).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "list_drop".to_string(),
                    "list_append".to_string(),
                    "list_length".to_string(),
                    "list_tail".to_string(),
                    "Nat.rec".to_string(),
                    "Nat.pred".to_string(),
                    "Nat.sub".to_string(),
                    "ListType.rec".to_string(),
                    "Le".to_string(),
                    "Le.rec".to_string(),
                    "Empty.rec".to_string(),
                    "Eq.substType".to_string(),
                    "nat_sub_self".to_string(),
                    "nat_sub_zero_right".to_string(),
                    "list_drop_zero".to_string(),
                    "list_drop_succ".to_string(),
                    "list_tail_cons".to_string(),
                    "list_append_cons".to_string(),
                    "list_length_cons".to_string(),
                    "list_length_nil".to_string(),
                    "nat_sub_succ_succ".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // 2. list_take_append_le: if n <= length xs then list_take n (xs ++ [a])
        // = list_take n xs — the appended tail is never reached by a take within
        // xs. Same skeleton as #1 (Le.rec -> Nat.sub = 0; Nat.rec on n; ListType.rec
        // on xs; absurd nil/succ via Empty.rec) but using the list_take unfolds.
        {
            let discr = "(Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat))";
            let succ_eq_zero = concat!(
                "(Eq.trans Nat (Nat.succ m) (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) Nat.zero ",
                "(Eq.symm Nat (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) (Nat.succ m) ",
                "(Eq.trans Nat (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) (Nat.sub (Nat.succ m) Nat.zero) (Nat.succ m) ",
                "(Eq.cong Nat Nat (fun (y : Nat) => Nat.sub (Nat.succ m) y) (list_length (ListType.nil KExpr)) Nat.zero (list_length_nil)) ",
                "(nat_sub_zero_right (Nat.succ m)))) ",
                "h_nil)"
            );
            let nil_absurd = format!(
                concat!(
                    "(fun (h_nil : Eq Nat (Nat.sub (Nat.succ m) (list_length (ListType.nil KExpr))) Nat.zero) => ",
                    "Empty.rec (fun (_ : Empty) => Eq (ListType KExpr) ",
                    "(list_take (Nat.succ m) (list_append (ListType.nil KExpr) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_take (Nat.succ m) (ListType.nil KExpr))) ",
                    "(Eq.substType Nat {discr} (Nat.succ m) Nat.zero {succ_eq_zero} (Nat.succ m)))"
                ),
                discr = discr,
                succ_eq_zero = succ_eq_zero,
            );

            // cons case. h_cons : Nat.sub (succ m) (length (x::rest)) = 0.
            // LHS take (succ m) ((x::rest)++[a]) = take (succ m)(x::(rest++[a]))
            //   = x :: take m (rest++[a])  [take_succ_cons]
            // ih rest : take m (rest++[a]) = take m rest, so LHS = x :: take m rest.
            // RHS take (succ m)(x::rest) = x :: take m rest. Equal.
            let cons_case = concat!(
                "(fun (x : KExpr) (rest : ListType KExpr) ",
                "(_ihinner : Eq Nat (Nat.sub (Nat.succ m) (list_length rest)) Nat.zero -> ",
                "Eq (ListType KExpr) (list_take (Nat.succ m) (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_take (Nat.succ m) rest)) ",
                "(h_cons : Eq Nat (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) Nat.zero) => ",
                "(fun (sub_m_rest : Eq Nat (Nat.sub m (list_length rest)) Nat.zero) => ",
                "Eq.trans (ListType KExpr) ",
                "(list_take (Nat.succ m) (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(ListType.cons KExpr x (list_take m rest)) ",
                "(list_take (Nat.succ m) (ListType.cons KExpr x rest)) ",
                // LEG A: LHS = x :: take m rest
                "(Eq.trans (ListType KExpr) ",
                "(list_take (Nat.succ m) (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_take (Nat.succ m) (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))) ",
                "(ListType.cons KExpr x (list_take m rest)) ",
                // append cons
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_take (Nat.succ m) L) ",
                "(list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                "(ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(list_append_cons x rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                // take_succ_cons: take (succ m)(x::L) = x :: take m L; then ih on the tail
                "(Eq.trans (ListType KExpr) ",
                "(list_take (Nat.succ m) (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))) ",
                "(ListType.cons KExpr x (list_take m (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))))) ",
                "(ListType.cons KExpr x (list_take m rest)) ",
                "(list_take_succ_cons m x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => ListType.cons KExpr x L) ",
                "(list_take m (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) (list_take m rest) ",
                "(_ihinner_m rest sub_m_rest)))) ",
                // LEG B: x :: take m rest = take (succ m)(x::rest)
                "(Eq.symm (ListType KExpr) ",
                "(list_take (Nat.succ m) (ListType.cons KExpr x rest)) ",
                "(ListType.cons KExpr x (list_take m rest)) ",
                "(list_take_succ_cons m x rest))) ",
                // sub_m_rest derivation
                "(Eq.trans Nat (Nat.sub m (list_length rest)) (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) Nat.zero ",
                "(Eq.symm Nat (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) (Nat.sub m (list_length rest)) ",
                "(Eq.trans Nat (Nat.sub (Nat.succ m) (list_length (ListType.cons KExpr x rest))) (Nat.sub (Nat.succ m) (Nat.succ (list_length rest))) (Nat.sub m (list_length rest)) ",
                "(Eq.cong Nat Nat (fun (y : Nat) => Nat.sub (Nat.succ m) y) (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) (list_length_cons x rest)) ",
                "(nat_sub_succ_succ m (list_length rest)))) ",
                "h_cons))"
            );

            let succ_arm = format!(
                concat!(
                    "(fun (m : Nat) ",
                    "(_ihinner_m : forall (xs0 : ListType KExpr), Eq Nat (Nat.sub m (list_length xs0)) Nat.zero -> ",
                    "Eq (ListType KExpr) (list_take m (list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_take m xs0)) => ",
                    "fun (xs0 : ListType KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq Nat (Nat.sub (Nat.succ m) (list_length xs1)) Nat.zero -> ",
                    "Eq (ListType KExpr) (list_take (Nat.succ m) (list_append xs1 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_take (Nat.succ m) xs1)) ",
                    "{nil_absurd} ",
                    "{cons_case} ",
                    "xs0)"
                ),
                nil_absurd = nil_absurd,
                cons_case = cons_case,
            );

            // zero arm: take 0 (xs++[a]) = nil = take 0 xs.
            let zero_arm = concat!(
                "(fun (xs0 : ListType KExpr) (_h0 : Eq Nat (Nat.sub Nat.zero (list_length xs0)) Nat.zero) => ",
                "Eq.trans (ListType KExpr) ",
                "(list_take Nat.zero (list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(ListType.nil KExpr) ",
                "(list_take Nat.zero xs0) ",
                "(list_take_zero (list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                "(Eq.symm (ListType KExpr) (list_take Nat.zero xs0) (ListType.nil KExpr) (list_take_zero xs0)))"
            );

            let le_to_sub = concat!(
                "(Le.rec n (fun (j : Nat) (_ : Le n j) => Eq Nat (Nat.sub n j) Nat.zero) ",
                "(nat_sub_self n) ",
                "(fun (m : Nat) (_h : Le n m) (ihm : Eq Nat (Nat.sub n m) Nat.zero) => ",
                "Eq.trans Nat (Nat.sub n (Nat.succ m)) (Nat.pred (Nat.sub n m)) Nat.zero ",
                "(Eq.refl Nat (Nat.pred (Nat.sub n m))) ",
                "(Eq.trans Nat (Nat.pred (Nat.sub n m)) (Nat.pred Nat.zero) Nat.zero ",
                "(Eq.cong Nat Nat Nat.pred (Nat.sub n m) Nat.zero ihm) (Eq.refl Nat Nat.zero))) ",
                "(list_length xs) hle)"
            );

            let value = format!(
                concat!(
                    "fun (n : Nat) (xs : ListType KExpr) (a : KExpr) (hle : Le n (list_length xs)) => ",
                    "(fun (hsub : Eq Nat (Nat.sub n (list_length xs)) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (xs0 : ListType KExpr), Eq Nat (Nat.sub n0 (list_length xs0)) Nat.zero -> ",
                    "Eq (ListType KExpr) (list_take n0 (list_append xs0 (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                    "(list_take n0 xs0)) ",
                    "{zero_arm} ",
                    "{succ_arm} ",
                    "n xs hsub) ",
                    "{le_to_sub}"
                ),
                zero_arm = zero_arm.replace("a0", "a"),
                succ_arm = succ_arm.replace("a0", "a"),
                le_to_sub = le_to_sub,
            );

            self.add_definition(SpecDefinition {
                name: "list_take_append_le".to_string(),
                type_src: concat!(
                    "forall (n : Nat) (xs : ListType KExpr) (a : KExpr), ",
                    "Le n (list_length xs) -> ",
                    "Eq (ListType KExpr) (list_take n (list_append xs (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                    "(list_take n xs)"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "If n <= length xs then list_take n (xs ++ [a]) = list_take n xs: a take within xs never reaches the appended tail. Same induction skeleton as list_drop_append_ge using the list_take unfolds. DerivedProved, zero axiom_deps. Part of #2859 (iota,app over-application).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "list_take".to_string(),
                    "list_append".to_string(),
                    "list_length".to_string(),
                    "Nat.rec".to_string(),
                    "Nat.pred".to_string(),
                    "Nat.sub".to_string(),
                    "ListType.rec".to_string(),
                    "Le".to_string(),
                    "Le.rec".to_string(),
                    "Empty.rec".to_string(),
                    "Eq.substType".to_string(),
                    "nat_sub_self".to_string(),
                    "nat_sub_zero_right".to_string(),
                    "list_take_zero".to_string(),
                    "list_take_succ_cons".to_string(),
                    "list_append_cons".to_string(),
                    "list_length_cons".to_string(),
                    "list_length_nil".to_string(),
                    "nat_sub_succ_succ".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // list_drop_nil: list_drop k [] = [] for all k. Nat.rec on k: zero via
        // list_drop_zero; succ via list_drop_succ + list_tail_nil + IH.
        self.add_definition(SpecDefinition {
            name: "list_drop_nil".to_string(),
            type_src: "forall (k : Nat), Eq (ListType KExpr) (list_drop k (ListType.nil KExpr)) (ListType.nil KExpr)".to_string(),
            value_src: Some(
                concat!(
                    "fun (k : Nat) => Nat.rec ",
                    "(fun (k0 : Nat) => Eq (ListType KExpr) (list_drop k0 (ListType.nil KExpr)) (ListType.nil KExpr)) ",
                    // zero
                    "(list_drop_zero (ListType.nil KExpr)) ",
                    // succ: list_drop (succ m) nil = list_drop m (tail nil) = list_drop m nil = nil
                    "(fun (m : Nat) (ih : Eq (ListType KExpr) (list_drop m (ListType.nil KExpr)) (ListType.nil KExpr)) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (ListType.nil KExpr)) ",
                    "(list_drop m (list_tail (ListType.nil KExpr))) ",
                    "(ListType.nil KExpr) ",
                    "(list_drop_succ m (ListType.nil KExpr)) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_drop m (list_tail (ListType.nil KExpr))) ",
                    "(list_drop m (ListType.nil KExpr)) ",
                    "(ListType.nil KExpr) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                    "(list_tail (ListType.nil KExpr)) (ListType.nil KExpr) list_tail_nil) ",
                    "ih)) ",
                    "k"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "list_drop k [] = [] for all k. Nat.rec on k via list_drop_zero / list_drop_succ + list_tail_nil. DerivedProved, zero axiom_deps. Part of #2859 (iota,app over-application).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "list_drop".to_string(),
                "list_tail".to_string(),
                "Nat.rec".to_string(),
                "list_drop_zero".to_string(),
                "list_drop_succ".to_string(),
                "list_tail_nil".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // 3. list_head_drop_append_some: the major-premise stability. If the head
        // of (drop k xs) is some major (the major premise lies within xs), then
        // appending [a] past the window leaves the head of (drop k (xs ++ [a]))
        // unchanged = some major. Nat.rec on k (motive generalizes xs); each k
        // case-splits xs (ListType.rec). The nil sub-case is impossible (head of
        // an empty drop is none, contradicting the some hypothesis) — discharged
        // via list_drop_nil + option_none_ne_some.
        {
            // nil sub-case: list_head (list_drop K nil) = some major is absurd.
            // K is the current drop count (Nat.zero in the zero arm, Nat.succ m in
            // the succ arm). Parameterized by the drop-count expression KCNT and
            // the goal MOTIVE-instance via a thunk.
            let nil_absurd = |kcnt: &str, goal: &str| -> String {
                format!(
                    concat!(
                        "(fun (h_nil : Eq (OptionType KExpr) (list_head (list_drop {kcnt} (ListType.nil KExpr))) (OptionType.some KExpr major)) => ",
                        "option_none_ne_some KExpr major ({goal}) ",
                        "(Eq.trans (OptionType KExpr) ",
                        "(OptionType.none KExpr) ",
                        "(list_head (list_drop {kcnt} (ListType.nil KExpr))) ",
                        "(OptionType.some KExpr major) ",
                        // none = list_head (list_drop kcnt nil): symm of (drop kcnt nil = nil ; head nil = none)
                        "(Eq.symm (OptionType KExpr) ",
                        "(list_head (list_drop {kcnt} (ListType.nil KExpr))) (OptionType.none KExpr) ",
                        "(Eq.trans (OptionType KExpr) ",
                        "(list_head (list_drop {kcnt} (ListType.nil KExpr))) ",
                        "(list_head (ListType.nil KExpr)) ",
                        "(OptionType.none KExpr) ",
                        "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                        "(list_drop {kcnt} (ListType.nil KExpr)) (ListType.nil KExpr) (list_drop_nil {kcnt})) ",
                        "list_head_nil)) ",
                        "h_nil))"
                    ),
                    kcnt = kcnt,
                    goal = goal,
                )
            };

            // zero arm: h : list_head (list_drop 0 xs) = some major i.e. head xs.
            // Goal: list_head (list_drop 0 (xs++[a])) = some major i.e. head (xs++[a]).
            let zero_goal = "Eq (OptionType KExpr) (list_head (list_drop Nat.zero (list_append (ListType.nil KExpr) (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)";
            let zero_cons = concat!(
                "(fun (x : KExpr) (rest : ListType KExpr) ",
                "(_ihc : Eq (OptionType KExpr) (list_head (list_drop Nat.zero rest)) (OptionType.some KExpr major) -> ",
                "Eq (OptionType KExpr) (list_head (list_drop Nat.zero (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)) ",
                "(_h : Eq (OptionType KExpr) (list_head (list_drop Nat.zero (ListType.cons KExpr x rest))) (OptionType.some KExpr major)) => ",
                // goal: head (drop 0 ((x::rest)++[a])) = some major.
                // drop 0 L = L; (x::rest)++[a] = x::(rest++[a]); head (x::_) = some x.
                // From _h : head (drop 0 (x::rest)) = some major, i.e. some x = some major.
                "Eq.trans (OptionType KExpr) ",
                "(list_head (list_drop Nat.zero (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(OptionType.some KExpr x) ",
                "(OptionType.some KExpr major) ",
                // LHS = some x
                "(Eq.trans (OptionType KExpr) ",
                "(list_head (list_drop Nat.zero (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(list_head (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(OptionType.some KExpr x) ",
                "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                "(list_drop Nat.zero (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr))) ",
                "(list_drop_zero (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(Eq.trans (OptionType KExpr) ",
                "(list_head (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_head (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(OptionType.some KExpr x) ",
                "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                "(list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr))) ",
                "(ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_append_cons x rest (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_head_cons x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))))) ",
                // some x = some major, from _h (head (drop 0 (x::rest)) = some major)
                "(Eq.trans (OptionType KExpr) (OptionType.some KExpr x) ",
                "(list_head (list_drop Nat.zero (ListType.cons KExpr x rest))) ",
                "(OptionType.some KExpr major) ",
                "(Eq.symm (OptionType KExpr) ",
                "(list_head (list_drop Nat.zero (ListType.cons KExpr x rest))) (OptionType.some KExpr x) ",
                "(Eq.trans (OptionType KExpr) ",
                "(list_head (list_drop Nat.zero (ListType.cons KExpr x rest))) ",
                "(list_head (ListType.cons KExpr x rest)) ",
                "(OptionType.some KExpr x) ",
                "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                "(list_drop Nat.zero (ListType.cons KExpr x rest)) (ListType.cons KExpr x rest) ",
                "(list_drop_zero (ListType.cons KExpr x rest))) ",
                "(list_head_cons x rest))) ",
                "_h))"
            );
            let zero_arm = format!(
                concat!(
                    "(fun (xs0 : ListType KExpr) ",
                    "(h : Eq (OptionType KExpr) (list_head (list_drop Nat.zero xs0)) (OptionType.some KExpr major)) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq (OptionType KExpr) (list_head (list_drop Nat.zero xs1)) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop Nat.zero (list_append xs1 (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)) ",
                    "{nil_absurd} ",
                    "{zero_cons} ",
                    "xs0 h)"
                ),
                nil_absurd = nil_absurd("Nat.zero", zero_goal),
                zero_cons = zero_cons,
            );

            // succ arm. k = succ m. ih : MOTIVE m. xs case-split.
            // cons x rest: drop (succ m)(x::rest) = drop m rest; (x::rest)++[a] =
            // x::(rest++[a]); drop (succ m)(x::(rest++[a])) = drop m (rest++[a]).
            // So goal head (drop m (rest++[a])) = some major; h gives head (drop m rest)
            // = some major; apply outer ih at rest.
            let succ_cons = concat!(
                "(fun (x : KExpr) (rest : ListType KExpr) ",
                "(_ihc : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) rest)) (OptionType.some KExpr major) -> ",
                "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)) ",
                "(h : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (ListType.cons KExpr x rest))) (OptionType.some KExpr major)) => ",
                // goal LHS: head (drop (succ m) ((x::rest)++[a])) = head (drop m (rest++[a]))
                "Eq.trans (OptionType KExpr) ",
                "(list_head (list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(list_head (list_drop m (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(OptionType.some KExpr major) ",
                // LHS = head (drop m (rest++[a]))
                "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                "(list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_drop m (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(Eq.trans (ListType KExpr) ",
                "(list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(list_drop m (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop (Nat.succ m) L) ",
                "(list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a (ListType.nil KExpr))) ",
                "(ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_append_cons x rest (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(Eq.trans (ListType KExpr) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(list_drop m (list_tail (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))))) ",
                "(list_drop m (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_drop_succ m (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                "(list_tail (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr))))) ",
                "(list_append rest (ListType.cons KExpr a (ListType.nil KExpr))) ",
                "(list_tail_cons x (list_append rest (ListType.cons KExpr a (ListType.nil KExpr)))))))) ",
                // head (drop m (rest++[a])) = some major via ih on rest with h_rest
                "(_ihinner_m rest ",
                // h_rest : head (drop m rest) = some major, from h.
                "(Eq.trans (OptionType KExpr) ",
                "(list_head (list_drop m rest)) ",
                "(list_head (list_drop (Nat.succ m) (ListType.cons KExpr x rest))) ",
                "(OptionType.some KExpr major) ",
                "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                "(list_drop m rest) (list_drop (Nat.succ m) (ListType.cons KExpr x rest)) ",
                "(Eq.symm (ListType KExpr) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x rest)) (list_drop m rest) ",
                "(Eq.trans (ListType KExpr) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x rest)) ",
                "(list_drop m (list_tail (ListType.cons KExpr x rest))) ",
                "(list_drop m rest) ",
                "(list_drop_succ m (ListType.cons KExpr x rest)) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                "(list_tail (ListType.cons KExpr x rest)) rest (list_tail_cons x rest))))) ",
                "h)))"
            );
            let succ_goal = "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (list_append (ListType.nil KExpr) (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)";
            let succ_arm = format!(
                concat!(
                    "(fun (m : Nat) ",
                    "(_ihinner_m : forall (xs0 : ListType KExpr), Eq (OptionType KExpr) (list_head (list_drop m xs0)) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop m (list_append xs0 (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)) => ",
                    "fun (xs0 : ListType KExpr) ",
                    "(h : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) xs0)) (OptionType.some KExpr major)) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) xs1)) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (list_append xs1 (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)) ",
                    "{nil_absurd} ",
                    "{succ_cons} ",
                    "xs0 h)"
                ),
                nil_absurd = nil_absurd("(Nat.succ m)", succ_goal),
                succ_cons = succ_cons,
            );

            let value = format!(
                concat!(
                    "fun (k : Nat) (xs : ListType KExpr) (a : KExpr) (major : KExpr) ",
                    "(hin : Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr major)) => ",
                    "Nat.rec ",
                    "(fun (k0 : Nat) => forall (xs0 : ListType KExpr), Eq (OptionType KExpr) (list_head (list_drop k0 xs0)) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop k0 (list_append xs0 (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)) ",
                    "{zero_arm} ",
                    "{succ_arm} ",
                    "k xs hin"
                ),
                zero_arm = zero_arm,
                succ_arm = succ_arm,
            );

            self.add_definition(SpecDefinition {
                name: "list_head_drop_append_some".to_string(),
                type_src: concat!(
                    "forall (k : Nat) (xs : ListType KExpr) (a : KExpr) (major : KExpr), ",
                    "Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop k (list_append xs (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major)"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "Major-premise stability: if the head of (drop k xs) is some major then appending [a] past the window leaves head (drop k (xs ++ [a])) = some major. Nat.rec on k / ListType.rec on xs; the empty-drop sub-case is impossible (none /= some) via list_drop_nil + option_none_ne_some. DerivedProved, zero axiom_deps. Part of #2859 (iota,app over-application).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "list_head".to_string(),
                    "list_drop".to_string(),
                    "list_append".to_string(),
                    "list_tail".to_string(),
                    "Nat.rec".to_string(),
                    "ListType.rec".to_string(),
                    "option_none_ne_some".to_string(),
                    "list_drop_nil".to_string(),
                    "list_drop_zero".to_string(),
                    "list_drop_succ".to_string(),
                    "list_tail_cons".to_string(),
                    "list_append_cons".to_string(),
                    "list_head_cons".to_string(),
                    "list_head_nil".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // 4. iota_reduct_app_over: the over-application identity. If f is an
        // over-applied iota redex with iota_reduct env f = some f1, and the major
        // window plus rule prefix both lie strictly within kapp_args f (the two
        // Le side-conditions hov/hovp), then iota_reduct env (app f a) = some
        // (app f1 a): the extra arg a rides along untouched past the reduct
        // spine. Inverts iota_reduct env f via iota_reduct_some_inv, then rebuilds
        // the (app f a) opt_bind chain with opt_bind_some_intro, transporting each
        // spine segment over the appended [a] via list_drop_append_ge (#1),
        // list_take_append_le (#2), list_head_drop_append_some (#3) and
        // apply_spine_snoc, finishing with option_some_inj.
        self.add_definition(SpecDefinition {
            name: "iota_reduct_app_over".to_string(),
            type_src: r#"forall (env : RecEnv) (f : KExpr) (a : KExpr) (f1 : KExpr), (forall (rn : Name) (m0 : RecMeta), Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) -> Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0) -> Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params m0) (recmeta_num_motives m0)) (recmeta_num_minors m0)) (recmeta_num_indices m0))) (list_length (kapp_args f))) -> (forall (rn : Name) (m0 : RecMeta), Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) -> Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0) -> Le (Nat.add (Nat.add (recmeta_num_params m0) (recmeta_num_motives m0)) (recmeta_num_minors m0)) (list_length (kapp_args f))) -> Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f1 a))"#.to_string(),
            value_src: Some(r#"fun (env : RecEnv) (f : KExpr) (a : KExpr) (f1 : KExpr) (hov : (forall (rn : Name) (m0 : RecMeta), Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) -> Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0) -> Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params m0) (recmeta_num_motives m0)) (recmeta_num_minors m0)) (recmeta_num_indices m0))) (list_length (kapp_args f)))) (hovp : (forall (rn : Name) (m0 : RecMeta), Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) -> Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0) -> Le (Nat.add (Nat.add (recmeta_num_params m0) (recmeta_num_motives m0)) (recmeta_num_minors m0)) (list_length (kapp_args f)))) (h : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => iota_reduct_some_inv env f f1 (Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f1 a))) h (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname)) (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f))) (OptionType.some KExpr major)) (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) (h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))))) (OptionType.some KExpr f1)) => opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn (KExpr.app f a))) (fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))))))) recname (KExpr.app f1 a) (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a)) h1) (opt_bind_some_intro RecMeta KExpr (recmeta_for env recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule)))))))) meta (KExpr.app f1 a) h2 (opt_bind_some_intro KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))))) major (KExpr.app f1 a) (Eq.trans (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major) (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) L)) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a)) (list_head_drop_append_some (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f) a major h3)) (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule)))))) cname (KExpr.app f1 a) h4 (opt_bind_some_intro RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))) rule (KExpr.app f1 a) h5 (Eq.trans (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))) (OptionType.some KExpr (KExpr.app (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) a)) (OptionType.some KExpr (KExpr.app f1 a)) (Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr X) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule)))) (KExpr.app (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) a) (Eq.trans KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule)))) (apply_spine (list_append (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (ListType.cons KExpr a (ListType.nil KExpr))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) (KExpr.app (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) a) (Eq.trans KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule)))) (apply_spine (list_append (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (ListType.cons KExpr a (ListType.nil KExpr))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule)))) (apply_spine (list_append (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (ListType.cons KExpr a (ListType.nil KExpr))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) (Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule)))) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (list_append (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (ListType.cons KExpr a (ListType.nil KExpr))) (Eq.trans (ListType KExpr) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))) (list_append (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (ListType.cons KExpr a (ListType.nil KExpr))) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) L) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a)) (list_drop_append_ge (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f) a (hov recname meta h1 h2)))) (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine (list_append (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (ListType.cons KExpr a (ListType.nil KExpr))) Z) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))) (Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine L (recrule_rhs rule))) (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (Eq.trans (ListType KExpr) (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))) (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) L) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a)) (list_take_append_le (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f) a (hovp recname meta h1 h2)))))) (apply_spine_snoc (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) a (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))))) (Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr (KExpr.app X a)) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) f1 (option_some_inj KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) f1 h5r))))))))"#.to_string()),
            is_axiom: false,
            description: "Over-application identity for iota: if iota_reduct env f = some f1 and the recursor's major window + rule prefix lie within kapp_args f (the Le side-conditions), then iota_reduct env (app f a) = some (app f1 a). The extra over-applied arg rides untouched past the reduct spine. Inverts via iota_reduct_some_inv, rebuilds the chain with opt_bind_some_intro x5, transporting each spine segment over [a] via list_drop_append_ge / list_take_append_le / list_head_drop_append_some / apply_spine_snoc, then option_some_inj. DerivedProved, zero axiom_deps. Part of #2859 (iota,app over-application).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "list_drop_append_ge".to_string(),
                    "list_take_append_le".to_string(),
                    "list_head_drop_append_some".to_string(),
                    "apply_spine_snoc".to_string(),
                    "kapp_args_app".to_string(),
                    "kapp_fn_app".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =====================================================================
        // (a)-join substrate (#2859 (iota,app) MINIMAL-redex join): the
        // Le-internalization helpers so iota_reduct_app_some can derive the
        // over-application side-conditions from the redex witness alone.
        // =====================================================================

        // le_zero_n: Le 0 n for all n. Nat.rec on n; zero via Le.refl 0, succ via
        // Le.step.
        self.add_definition(SpecDefinition {
            name: "le_zero_n".to_string(),
            type_src: "forall (n : Nat), Le Nat.zero n".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) => Nat.rec (fun (n0 : Nat) => Le Nat.zero n0) ",
                    "(Le.refl Nat.zero) ",
                    "(fun (m : Nat) (ih : Le Nat.zero m) => Le.step Nat.zero m ih) ",
                    "n"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le 0 n for all n: Nat.rec on n (Le.refl base, Le.step succ). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.refl".to_string(),
                "Le.step".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // le_succ_succ: Le a b -> Le (succ a) (succ b). Le.rec on the proof; the
        // first index a is promoted to a PARAMETER, so the motive ranges over the
        // second index only. refl arm: Le (succ a) (succ a) via Le.refl; step arm:
        // Le (succ a) (succ (succ m)) from Le (succ a) (succ m) via Le.step.
        self.add_definition(SpecDefinition {
            name: "le_succ_succ".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Le a b -> Le (Nat.succ a) (Nat.succ b)"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (h : Le a b) => ",
                    "Le.rec a (fun (j : Nat) (_ : Le a j) => Le (Nat.succ a) (Nat.succ j)) ",
                    "(Le.refl (Nat.succ a)) ",
                    "(fun (m : Nat) (_hm : Le a m) (ihm : Le (Nat.succ a) (Nat.succ m)) => ",
                    "Le.step (Nat.succ a) (Nat.succ m) ihm) ",
                    "b h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le a b -> Le (succ a) (succ b). Le.rec on the proof (a promoted to parameter; motive over the 2nd index): refl via Le.refl (succ a), step via Le.step. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.refl".to_string(),
                "Le.step".to_string(),
                "Le.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // (nat_add_zero_right and nat_add_succ_right are already registered in
        // foundation_arith_lemmas.rs; reused below.)

        // le_trans: Le a b -> Le b c -> Le a c. Le.rec on the second proof (b
        // promoted to parameter, motive over c): refl arm c=b returns hab; step arm
        // Le a (succ m) from Le a m (IH) via Le.step.
        self.add_definition(SpecDefinition {
            name: "le_trans".to_string(),
            type_src: "forall (a : Nat) (b : Nat) (c : Nat), Le a b -> Le b c -> Le a c"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) (hab : Le a b) (hbc : Le b c) => ",
                    "Le.rec b (fun (j : Nat) (_ : Le b j) => Le a j) ",
                    "hab ",
                    "(fun (m : Nat) (_hm : Le b m) (ihm : Le a m) => Le.step a m ihm) ",
                    "c hbc"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Transitivity of Le: Le a b -> Le b c -> Le a c. Le.rec on the second proof (b parameter, motive over c): refl arm returns hab, step arm via Le.step. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.step".to_string(),
                "Le.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // le_add_self_left: Le a (a + b). Nat.rec on b; zero via nat_add_zero_right
        // + Le.refl, succ via nat_add_succ_right + Le.step on the IH.
        self.add_definition(SpecDefinition {
            name: "le_add_self_left".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Le a (Nat.add a b)".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) => ",
                    "Nat.rec (fun (b0 : Nat) => Le a (Nat.add a b0)) ",
                    // zero: Le a (a + 0); transport Le a a along (a = a + 0).
                    "(Eq.subst Nat (fun (z : Nat) => Le a z) a (Nat.add a Nat.zero) ",
                    "(Eq.symm Nat (Nat.add a Nat.zero) a (nat_add_zero_right a)) ",
                    "(Le.refl a)) ",
                    // succ: Le a (a + succ m); from IH Le a (a + m), Le.step gives
                    // Le a (succ (a + m)); transport along (succ (a+m) = a + succ m).
                    "(fun (m : Nat) (ih : Le a (Nat.add a m)) => ",
                    "Eq.subst Nat (fun (z : Nat) => Le a z) (Nat.succ (Nat.add a m)) (Nat.add a (Nat.succ m)) ",
                    "(Eq.symm Nat (Nat.add a (Nat.succ m)) (Nat.succ (Nat.add a m)) (nat_add_succ_right a m)) ",
                    "(Le.step a (Nat.add a m) ih)) ",
                    "b"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le a (a + b): a is below its right-sum. Nat.rec on b; zero via nat_add_zero_right + Le.refl, succ via nat_add_succ_right + Le.step on the IH. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.refl".to_string(),
                "Le.step".to_string(),
                "Nat.rec".to_string(),
                "Nat.add".to_string(),
                "nat_add_zero_right".to_string(),
                "nat_add_succ_right".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_head_drop_some_le_succ: the redex window lies within the spine — if
        // the head of (drop k xs) is some y then k < length xs, i.e. Le (succ k)
        // (length xs). This internalizes the major-window side-condition for the
        // (iota,app) minimal join: iota_reduct env f = some f1 supplies (via
        // iota_reduct_some_inv) exactly head (drop major_idx (kapp_args f)) = some
        // major, whence Le (succ major_idx) (length (kapp_args f)). Nat.rec on k
        // (motive generalizing xs); each k case-splits xs (ListType.rec). The
        // empty-drop sub-case (head of an empty drop is none) is impossible —
        // discharged via list_drop_nil + list_head_nil + option_none_ne_some.
        {
            // nil sub-case for drop-count KCNT: head (drop KCNT nil) = some y is
            // absurd; return any GOAL via option_none_ne_some.
            let nil_absurd = |kcnt: &str| -> String {
                format!(
                    concat!(
                        "(fun (h_nil : Eq (OptionType KExpr) (list_head (list_drop {kcnt} (ListType.nil KExpr))) (OptionType.some KExpr y)) => ",
                        "option_none_ne_some KExpr y (Le (Nat.succ {kcnt}) (list_length (ListType.nil KExpr))) ",
                        "(Eq.trans (OptionType KExpr) ",
                        "(OptionType.none KExpr) ",
                        "(list_head (list_drop {kcnt} (ListType.nil KExpr))) ",
                        "(OptionType.some KExpr y) ",
                        // none = head (drop KCNT nil): symm of (drop KCNT nil = nil; head nil = none)
                        "(Eq.symm (OptionType KExpr) (list_head (list_drop {kcnt} (ListType.nil KExpr))) (OptionType.none KExpr) ",
                        "(Eq.trans (OptionType KExpr) ",
                        "(list_head (list_drop {kcnt} (ListType.nil KExpr))) ",
                        "(list_head (ListType.nil KExpr)) ",
                        "(OptionType.none KExpr) ",
                        "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                        "(list_drop {kcnt} (ListType.nil KExpr)) (ListType.nil KExpr) (list_drop_nil {kcnt})) ",
                        "list_head_nil)) ",
                        "h_nil))"
                    ),
                    kcnt = kcnt,
                )
            };

            // zero arm: forall xs0, head (drop 0 xs0) = some y -> Le (succ 0) (length xs0).
            let zero_cons = concat!(
                "(fun (x : KExpr) (rest : ListType KExpr) ",
                "(_ihc : Eq (OptionType KExpr) (list_head (list_drop Nat.zero rest)) (OptionType.some KExpr y) -> Le (Nat.succ Nat.zero) (list_length rest)) ",
                "(_h : Eq (OptionType KExpr) (list_head (list_drop Nat.zero (ListType.cons KExpr x rest))) (OptionType.some KExpr y)) => ",
                // Le (succ 0) (length (x::rest)); length (x::rest) = succ (length rest).
                "Eq.subst Nat (fun (z : Nat) => Le (Nat.succ Nat.zero) z) ",
                "(Nat.succ (list_length rest)) (list_length (ListType.cons KExpr x rest)) ",
                "(Eq.symm Nat (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) (list_length_cons x rest)) ",
                "(le_succ_succ Nat.zero (list_length rest) (le_zero_n (list_length rest))))"
            );
            let zero_arm = format!(
                concat!(
                    "(fun (xs0 : ListType KExpr) ",
                    "(h : Eq (OptionType KExpr) (list_head (list_drop Nat.zero xs0)) (OptionType.some KExpr y)) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq (OptionType KExpr) (list_head (list_drop Nat.zero xs1)) (OptionType.some KExpr y) -> Le (Nat.succ Nat.zero) (list_length xs1)) ",
                    "{nil_absurd} ",
                    "{zero_cons} ",
                    "xs0 h)"
                ),
                nil_absurd = nil_absurd("Nat.zero"),
                zero_cons = zero_cons,
            );

            // succ arm: m + ih (forall xs0, head (drop m xs0)=some y -> Le (succ m)(length xs0)).
            let succ_cons = concat!(
                "(fun (x : KExpr) (rest : ListType KExpr) ",
                "(_ihc : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) rest)) (OptionType.some KExpr y) -> Le (Nat.succ (Nat.succ m)) (list_length rest)) ",
                "(h : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (ListType.cons KExpr x rest))) (OptionType.some KExpr y)) => ",
                // head (drop (succ m)(x::rest)) = head (drop m rest); so ih rest applies.
                // Goal: Le (succ (succ m)) (length (x::rest)) = Le (succ(succ m))(succ(length rest)).
                "Eq.subst Nat (fun (z : Nat) => Le (Nat.succ (Nat.succ m)) z) ",
                "(Nat.succ (list_length rest)) (list_length (ListType.cons KExpr x rest)) ",
                "(Eq.symm Nat (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) (list_length_cons x rest)) ",
                "(le_succ_succ (Nat.succ m) (list_length rest) ",
                // ih rest applied to: head (drop m rest) = some y, derived from h.
                "(_ihinner rest ",
                "(Eq.trans (OptionType KExpr) ",
                "(list_head (list_drop m rest)) ",
                "(list_head (list_drop (Nat.succ m) (ListType.cons KExpr x rest))) ",
                "(OptionType.some KExpr y) ",
                // head (drop m rest) = head (drop (succ m)(x::rest)): symm of the unfold.
                "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                "(list_drop m rest) (list_drop (Nat.succ m) (ListType.cons KExpr x rest)) ",
                "(Eq.symm (ListType KExpr) (list_drop (Nat.succ m) (ListType.cons KExpr x rest)) (list_drop m rest) ",
                "(Eq.trans (ListType KExpr) ",
                "(list_drop (Nat.succ m) (ListType.cons KExpr x rest)) ",
                "(list_drop m (list_tail (ListType.cons KExpr x rest))) ",
                "(list_drop m rest) ",
                "(list_drop_succ m (ListType.cons KExpr x rest)) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                "(list_tail (ListType.cons KExpr x rest)) rest (list_tail_cons x rest))))) ",
                "h)))) "
            );
            let succ_arm = format!(
                concat!(
                    "(fun (m : Nat) ",
                    "(_ihinner : forall (xs0 : ListType KExpr), Eq (OptionType KExpr) (list_head (list_drop m xs0)) (OptionType.some KExpr y) -> Le (Nat.succ m) (list_length xs0)) => ",
                    "fun (xs0 : ListType KExpr) ",
                    "(h : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) xs0)) (OptionType.some KExpr y)) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) xs1)) (OptionType.some KExpr y) -> Le (Nat.succ (Nat.succ m)) (list_length xs1)) ",
                    "{nil_absurd} ",
                    "{succ_cons} ",
                    "xs0 h)"
                ),
                nil_absurd = nil_absurd("(Nat.succ m)"),
                succ_cons = succ_cons,
            );

            let value = format!(
                concat!(
                    "fun (k : Nat) (xs : ListType KExpr) (y : KExpr) ",
                    "(hin : Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr y)) => ",
                    "Nat.rec ",
                    "(fun (k0 : Nat) => forall (xs0 : ListType KExpr), Eq (OptionType KExpr) (list_head (list_drop k0 xs0)) (OptionType.some KExpr y) -> Le (Nat.succ k0) (list_length xs0)) ",
                    "{zero_arm} ",
                    "{succ_arm} ",
                    "k xs hin"
                ),
                zero_arm = zero_arm,
                succ_arm = succ_arm,
            );

            self.add_definition(SpecDefinition {
                name: "list_head_drop_some_le_succ".to_string(),
                type_src: concat!(
                    "forall (k : Nat) (xs : ListType KExpr) (y : KExpr), ",
                    "Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr y) -> ",
                    "Le (Nat.succ k) (list_length xs)"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "Redex window within the spine: head (drop k xs) = some y implies Le (succ k) (length xs). Nat.rec on k / ListType.rec on xs; the empty-drop sub-case is impossible (head of an empty drop is none) via list_drop_nil + list_head_nil + option_none_ne_some; the cons cases use le_succ_succ + le_zero_n. Internalizes the major-window side-condition for the (iota,app) minimal join. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "list_head".to_string(),
                    "list_drop".to_string(),
                    "list_length".to_string(),
                    "list_tail".to_string(),
                    "Nat.rec".to_string(),
                    "ListType.rec".to_string(),
                    "Le".to_string(),
                    "le_succ_succ".to_string(),
                    "le_zero_n".to_string(),
                    "option_none_ne_some".to_string(),
                    "list_drop_nil".to_string(),
                    "list_drop_succ".to_string(),
                    "list_tail_cons".to_string(),
                    "list_head_nil".to_string(),
                    "list_length_cons".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.subst".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_reduct_app_some (TASK A): internalize the Le side-conditions of
        // iota_reduct_app_over. From iota_step env f f1 alone (no explicit Le args),
        // derive iota_step env (app f a) (app f1 a). Inverts the redex witness via
        // iota_reduct_some_inv (recovering meta + h3: head (drop major_idx
        // (kapp_args f)) = some major), then calls iota_reduct_app_over supplying the
        // hov/hovp continuations. Each continuation receives (rn, m0) with proofs the
        // head/recmeta lookups give them; by option_some_inj on h1/h2 those coincide
        // with the inversion's (recname, meta), so the m0-arithmetic goal is rewritten
        // to meta-arithmetic via Eq.subst and discharged from h3:
        //   hov  : Le (succ major_idx(meta)) length  = list_head_drop_some_le_succ h3
        //   hovp : Le prefix(meta) length            = le_trans (le_add_self_left;Le.step) hov.
        {
            // arithmetic sub-terms over a metavariable M (parameterizable).
            let prefix_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m}))")
            };
            let majidx_of = |m: &str| -> String {
                format!(
                    "(Nat.add {prefix} (recmeta_num_indices {m}))",
                    prefix = prefix_of(m)
                )
            };
            let len_f = "(list_length (kapp_args f))";
            let prefix_meta = prefix_of("meta");
            let majidx_meta = majidx_of("meta");

            // m0 = meta, derived inside a continuation from h1 (outer head=some recname)
            // + h1' (inner head=some rn) + h2 (outer recmeta=some meta) + h2' (inner
            // recmeta_for env rn = some m0). First rn=recname via option_some_inj on
            // h1/h1', then rewrite h2' to recmeta_for env recname, then meta=m0.
            // Produces an Eq RecMeta meta m0 named via the expression below.
            // hrn_expr : Eq Name recname rn, from h1 (head=some recname) and h1'
            // (head=some rn) via option_some_inj on the common head lookup.
            let hrn_expr = concat!(
                "(option_some_inj Name recname rn ",
                "(Eq.trans (OptionType Name) (OptionType.some Name recname) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) ",
                "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname) h1) ",
                "h1'))"
            );
            // h2recname_expr : Eq (OptionType RecMeta) (recmeta_for env recname) (some m0),
            // by rewriting h2' (over rn) along rn=recname (symm hrn_expr).
            let h2recname_expr = format!(
                concat!(
                    "(Eq.substType Name (fun (n : Name) => Eq (OptionType RecMeta) (recmeta_for env n) (OptionType.some RecMeta m0)) rn recname ",
                    "(Eq.symm Name recname rn {hrn_expr}) h2')"
                ),
                hrn_expr = hrn_expr,
            );
            // meta_eq_m0 : Eq RecMeta meta m0, inlined (no beta-redexes) so type
            // inference sees option_some_inj's conclusion directly.
            let meta_eq_m0 = format!(
                concat!(
                    "(option_some_inj RecMeta meta m0 ",
                    "(Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta) (recmeta_for env recname) (OptionType.some RecMeta m0) ",
                    "(Eq.symm (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) h2) ",
                    "{h2recname_expr}))"
                ),
                h2recname_expr = h2recname_expr,
            );

            // hov continuation: fun rn m0 h1' h2' => Le (succ majidx(m0)) length.
            let hov = format!(
                concat!(
                    "(fun (rn : Name) (m0 : RecMeta) ",
                    "(h1' : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn)) ",
                    "(h2' : Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0)) => ",
                    // rewrite goal Le (succ majidx(m0)) len  <- Le (succ majidx(meta)) len  along meta=m0
                    "Eq.substType RecMeta (fun (mm : RecMeta) => Le (Nat.succ {majidx_mm}) {len_f}) meta m0 ",
                    "{meta_eq_m0} ",
                    "(list_head_drop_some_le_succ {majidx_meta} (kapp_args f) major h3))"
                ),
                majidx_mm = majidx_of("mm"),
                len_f = len_f,
                meta_eq_m0 = meta_eq_m0.as_str(),
                majidx_meta = majidx_meta,
            );

            // hovp continuation: fun rn m0 h1' h2' => Le prefix(m0) length.
            // Over meta: Le prefix(meta) len via le_trans(prefix<=majidx, majidx<=succ majidx, succ majidx<=len).
            let hbig_meta = format!(
                "(list_head_drop_some_le_succ {majidx_meta} (kapp_args f) major h3)",
                majidx_meta = majidx_meta,
            );
            let prefix_le_len_meta = format!(
                concat!(
                    "(le_trans {prefix_meta} (Nat.succ {majidx_meta}) {len_f} ",
                    // Le prefix(meta) (succ majidx(meta))
                    "(le_trans {prefix_meta} {majidx_meta} (Nat.succ {majidx_meta}) ",
                    // Le prefix(meta) majidx(meta) = le_add_self_left prefix indices
                    "(le_add_self_left {prefix_meta} (recmeta_num_indices meta)) ",
                    // Le majidx(meta) (succ majidx(meta))
                    "(Le.step {majidx_meta} {majidx_meta} (Le.refl {majidx_meta}))) ",
                    "{hbig_meta})"
                ),
                prefix_meta = prefix_meta,
                majidx_meta = majidx_meta,
                len_f = len_f,
                hbig_meta = hbig_meta,
            );
            let hovp = format!(
                concat!(
                    "(fun (rn : Name) (m0 : RecMeta) ",
                    "(h1' : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn)) ",
                    "(h2' : Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0)) => ",
                    "Eq.substType RecMeta (fun (mm : RecMeta) => Le {prefix_mm} {len_f}) meta m0 ",
                    "{meta_eq_m0} ",
                    "{prefix_le_len_meta})"
                ),
                prefix_mm = prefix_of("mm"),
                len_f = len_f,
                meta_eq_m0 = meta_eq_m0.as_str(),
                prefix_le_len_meta = prefix_le_len_meta,
            );

            // h3 type (as recovered by iota_reduct_some_inv) uses the explicit
            // major_idx form; the inversion's continuation binds exactly h1..h5,h5r.
            let h3_type = format!(
                "Eq (OptionType KExpr) (list_head (list_drop {majidx_meta} (kapp_args f))) (OptionType.some KExpr major)",
                majidx_meta = majidx_meta,
            );
            let h5r_reduct = format!(
                concat!(
                    "(apply_spine (list_drop (Nat.succ {majidx_meta}) (kapp_args f)) ",
                    "(apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) ",
                    "(apply_spine (list_take {prefix_meta} (kapp_args f)) (recrule_rhs rule))))"
                ),
                majidx_meta = majidx_meta,
                prefix_meta = prefix_meta,
            );

            let value = format!(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (a : KExpr) (f1 : KExpr) ",
                    "(hf : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => ",
                    "iota_reduct_some_inv env f f1 ",
                    "(Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f1 a))) ",
                    "hf ",
                    "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname)) ",
                    "(h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) ",
                    "(h3 : {h3_type}) ",
                    "(h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) ",
                    "(h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) ",
                    "(h5r : Eq (OptionType KExpr) (OptionType.some KExpr {h5r_reduct}) (OptionType.some KExpr f1)) => ",
                    "iota_reduct_app_over env f a f1 {hov} {hovp} hf)"
                ),
                h3_type = h3_type,
                h5r_reduct = h5r_reduct,
                hov = hov,
                hovp = hovp,
            );

            self.add_definition(SpecDefinition {
                name: "iota_reduct_app_some".to_string(),
                type_src: concat!(
                    "forall (env : RecEnv) (f : KExpr) (a : KExpr) (f1 : KExpr), ",
                    "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f1 a))"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "iota_step lifts over an applied arg WITHOUT explicit Le hypotheses (TASK A): iota_step env f f1 -> iota_step env (app f a) (app f1 a). Inverts the redex witness via iota_reduct_some_inv (recovering h3: head (drop major_idx (kapp_args f)) = some major), then applies iota_reduct_app_over with the Le side-conditions derived internally: hov from list_head_drop_some_le_succ on h3, hovp from le_trans (le_add_self_left, Le.step) on hov. The continuation's (rn,m0) are unified with (recname,meta) via option_some_inj on the head/recmeta lookups, rewriting the m0-arithmetic to meta-arithmetic. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "iota_reduct_app_over".to_string(),
                    "list_head_drop_some_le_succ".to_string(),
                    "le_trans".to_string(),
                    "le_add_self_left".to_string(),
                    "le_succ_succ".to_string(),
                    "Le".to_string(),
                    "Le.refl".to_string(),
                    "Le.step".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_reduct_app_none (TASK B): not-a-redex propagates from (app f a) to f.
        // If iota_reduct env (app f a) = none then iota_reduct env f = none.
        // Case-analysis on iota_reduct env f via OptionType.rec with the equation-
        // carrying motive M o := (iota_reduct env f = o) -> (iota_reduct env f = none):
        //   none arm  : the carried equation IS the goal.
        //   some f1 arm: iota_reduct_app_some lifts iota_reduct env f = some f1 to
        //               iota_reduct env (app f a) = some (app f1 a), contradicting the
        //               none hypothesis (none /= some) via option_none_ne_some.
        self.add_definition(SpecDefinition {
            name: "iota_reduct_app_none".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.none KExpr) -> ",
                "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (f : KExpr) (a : KExpr) ",
                    "(hnone : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.none KExpr)) => ",
                    "OptionType.rec KExpr ",
                    // motive: M o := (iota_reduct env f = o) -> (iota_reduct env f = none)
                    "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) (iota_reduct env f) o -> Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) ",
                    // none arm: the carried equation is the goal.
                    "(fun (heq : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) => heq) ",
                    // some arm: contradiction via iota_reduct_app_some + option_none_ne_some.
                    "(fun (f1 : KExpr) (heq : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => ",
                    "option_none_ne_some KExpr (KExpr.app f1 a) (Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(OptionType.none KExpr) ",
                    "(iota_reduct env (KExpr.app f a)) ",
                    "(OptionType.some KExpr (KExpr.app f1 a)) ",
                    "(Eq.symm (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.none KExpr) hnone) ",
                    "(iota_reduct_app_some env f a f1 heq))) ",
                    // scrutinee + reflexivity seed.
                    "(iota_reduct env f) ",
                    "(Eq.refl (OptionType KExpr) (iota_reduct env f))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Not-a-redex propagates over an applied arg (TASK B): iota_reduct env (app f a) = none -> iota_reduct env f = none. OptionType.rec case-analysis on iota_reduct env f with an equation-carrying motive; the none arm returns the carried equation, the some arm derives a contradiction from iota_reduct_app_some (which would force iota_reduct (app f a) = some _) against the none hypothesis via option_none_ne_some. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "iota_reduct_app_some".to_string(),
                "OptionType.rec".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // D.1 — list_head_drop_len_append (#2859 (iota,app) minimal join, par
        // analogue): dropping exactly (length xs) elements from xs ++ [a] leaves
        // [a], whose head is a. The boundary fact the par-reduct redex
        // reconstruction needs: the major premise sits at position length(args)
        // in the over-application kapp_args (app f a) = kapp_args f ++ [a], and
        // it IS the appended arg a. ListType.rec on xs: nil reduces the index to
        // 0 and append/[a]/head to some a; cons peels one element via
        // list_length_cons / list_append_cons / list_drop_succ / list_tail_cons,
        // landing on the IH (drop (length rest) (rest ++ [a])).
        {
            let cons_a = "(ListType.cons KExpr a (ListType.nil KExpr))";
            // The goal-shape predicate, parameterized by the concrete list L.
            let goal_for = |xs: &str| -> String {
                format!(
                    "Eq (OptionType KExpr) (list_head (list_drop (list_length {xs}) (list_append {xs} {cons_a}))) (OptionType.some KExpr a)"
                )
            };

            // nil arm: list_head (list_drop (length nil) (append nil [a])) = some a.
            //   length nil -> 0 ; drop 0 (append nil [a]) -> append nil [a] ;
            //   append nil [a] -> [a] ; head [a] -> some a.
            let nil_arm = format!(
                "(Eq.trans (OptionType KExpr) \
                 (list_head (list_drop (list_length (ListType.nil KExpr)) (list_append (ListType.nil KExpr) {cons_a}))) \
                 (list_head (list_drop Nat.zero (list_append (ListType.nil KExpr) {cons_a}))) \
                 (OptionType.some KExpr a) \
                 (Eq.cong Nat (OptionType KExpr) \
                 (fun (N : Nat) => list_head (list_drop N (list_append (ListType.nil KExpr) {cons_a}))) \
                 (list_length (ListType.nil KExpr)) Nat.zero list_length_nil) \
                 (Eq.trans (OptionType KExpr) \
                 (list_head (list_drop Nat.zero (list_append (ListType.nil KExpr) {cons_a}))) \
                 (list_head (list_append (ListType.nil KExpr) {cons_a})) \
                 (OptionType.some KExpr a) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) \
                 (list_drop Nat.zero (list_append (ListType.nil KExpr) {cons_a})) \
                 (list_append (ListType.nil KExpr) {cons_a}) \
                 (list_drop_zero (list_append (ListType.nil KExpr) {cons_a}))) \
                 (Eq.trans (OptionType KExpr) \
                 (list_head (list_append (ListType.nil KExpr) {cons_a})) \
                 (list_head {cons_a}) \
                 (OptionType.some KExpr a) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) \
                 (list_append (ListType.nil KExpr) {cons_a}) {cons_a} (list_append_nil {cons_a})) \
                 (list_head_cons a (ListType.nil KExpr)))))"
            );

            // cons arm: x rest ih, ih = goal_for(rest).
            //   LHS = head (drop (length (x::rest)) (append (x::rest) [a]))
            //       = head (drop (succ (length rest)) (x :: (rest ++ [a])))    [length_cons, append_cons]
            //       = head (drop (length rest) (tail (x :: (rest ++ [a]))))    [drop_succ]
            //       = head (drop (length rest) (rest ++ [a]))                  [tail_cons]
            //       = some a                                                   [ih]
            let ih_ty = goal_for("rest");
            let cons_arm = format!(
                "(fun (x : KExpr) (rest : ListType KExpr) (ih : {ih_ty}) => \
                 Eq.trans (OptionType KExpr) \
                 (list_head (list_drop (list_length (ListType.cons KExpr x rest)) (list_append (ListType.cons KExpr x rest) {cons_a}))) \
                 (list_head (list_drop (list_length rest) (list_append rest {cons_a}))) \
                 (OptionType.some KExpr a) \
                 (Eq.trans (OptionType KExpr) \
                 (list_head (list_drop (list_length (ListType.cons KExpr x rest)) (list_append (ListType.cons KExpr x rest) {cons_a}))) \
                 (list_head (list_drop (Nat.succ (list_length rest)) (list_append (ListType.cons KExpr x rest) {cons_a}))) \
                 (list_head (list_drop (list_length rest) (list_append rest {cons_a}))) \
                 (Eq.cong Nat (OptionType KExpr) \
                 (fun (N : Nat) => list_head (list_drop N (list_append (ListType.cons KExpr x rest) {cons_a}))) \
                 (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) (list_length_cons x rest)) \
                 (Eq.trans (OptionType KExpr) \
                 (list_head (list_drop (Nat.succ (list_length rest)) (list_append (ListType.cons KExpr x rest) {cons_a}))) \
                 (list_head (list_drop (Nat.succ (list_length rest)) (ListType.cons KExpr x (list_append rest {cons_a})))) \
                 (list_head (list_drop (list_length rest) (list_append rest {cons_a}))) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) \
                 (fun (L : ListType KExpr) => list_head (list_drop (Nat.succ (list_length rest)) L)) \
                 (list_append (ListType.cons KExpr x rest) {cons_a}) \
                 (ListType.cons KExpr x (list_append rest {cons_a})) \
                 (list_append_cons x rest {cons_a})) \
                 (Eq.trans (OptionType KExpr) \
                 (list_head (list_drop (Nat.succ (list_length rest)) (ListType.cons KExpr x (list_append rest {cons_a})))) \
                 (list_head (list_drop (list_length rest) (list_tail (ListType.cons KExpr x (list_append rest {cons_a}))))) \
                 (list_head (list_drop (list_length rest) (list_append rest {cons_a}))) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) \
                 (list_drop (Nat.succ (list_length rest)) (ListType.cons KExpr x (list_append rest {cons_a}))) \
                 (list_drop (list_length rest) (list_tail (ListType.cons KExpr x (list_append rest {cons_a})))) \
                 (list_drop_succ (list_length rest) (ListType.cons KExpr x (list_append rest {cons_a})))) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) \
                 (fun (L : ListType KExpr) => list_head (list_drop (list_length rest) L)) \
                 (list_tail (ListType.cons KExpr x (list_append rest {cons_a}))) \
                 (list_append rest {cons_a}) \
                 (list_tail_cons x (list_append rest {cons_a})))))) \
                 ih)"
            );

            let value = format!(
                "fun (xs : ListType KExpr) (a : KExpr) => \
                 ListType.rec KExpr \
                 (fun (xs0 : ListType KExpr) => {goal0}) \
                 {nil_arm} \
                 {cons_arm} \
                 xs",
                goal0 = goal_for("xs0"),
            );

            self.add_definition(SpecDefinition {
                name: "list_head_drop_len_append".to_string(),
                type_src: format!(
                    "forall (xs : ListType KExpr) (a : KExpr), {}",
                    goal_for("xs")
                ),
                value_src: Some(value),
                is_axiom: false,
                description: "Boundary head: dropping exactly (length xs) elements from xs ++ [a] leaves [a], whose head is some a. ListType.rec on xs; nil reduces index to 0 and append/[a]/head via list_length_nil / list_drop_zero / list_append_nil / list_head_cons; cons peels via list_length_cons / list_append_cons / list_drop_succ / list_tail_cons onto the IH. The boundary fact the par-reduct redex reconstruction (iota_reduct_par_app_redex) uses to locate the over-applied major at position length(kapp_args f). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "list_head".to_string(),
                    "list_drop".to_string(),
                    "list_length".to_string(),
                    "list_append".to_string(),
                    "list_tail".to_string(),
                    "ListType.rec".to_string(),
                    "list_length_nil".to_string(),
                    "list_length_cons".to_string(),
                    "list_drop_zero".to_string(),
                    "list_drop_succ".to_string(),
                    "list_append_nil".to_string(),
                    "list_append_cons".to_string(),
                    "list_tail_cons".to_string(),
                    "list_head_cons".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // D.2 — list_head_drop_append_some_inv (#2859 (iota,app) minimal join): the
        // CONVERSE of list_head_drop_append_some, gated by the STRICT window guard
        // Le (succ k) (length xs) (i.e. k < length xs). If the head of
        // (drop k (xs ++ [a])) is some major AND the drop window lies STRICTLY
        // inside xs, then appending [a] never reaches the window, so
        // head (drop k xs) = some major already. The strict guard is essential: at
        // the boundary k = length xs the appended a IS the major, and the
        // un-appended head is none, so the un-strict (Le k) version is FALSE. Same
        // induction skeleton as list_drop_append_ge: collapse Le (succ k)(length xs)
        // to Nat.sub (succ k)(length xs) = 0, then Nat.rec on k carrying that strict
        // guard (motive generalizes xs); each k case-splits xs (ListType.rec). The
        // nil corner is absurd (Nat.sub (succ _) 0 = succ _ /= 0) via Empty.rec on a
        // reduced discriminator.
        {
            let cons_a = "(ListType.cons KExpr a (ListType.nil KExpr))";
            // Discriminator: D z = Nat for z = succ _, Empty for z = zero.
            let discr = "(Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat))";

            // nil corner: the strict guard Nat.sub (succ KCNT) (length nil) = 0 is
            // absurd; collapse to succ KCNT = 0 and Empty.rec to the goal GOAL.
            let nil_absurd = |kcnt: &str, goal: &str| -> String {
                let succ_eq_zero = format!(
                    concat!(
                        "(Eq.trans Nat (Nat.succ {kcnt}) (Nat.sub (Nat.succ {kcnt}) (list_length (ListType.nil KExpr))) Nat.zero ",
                        "(Eq.symm Nat (Nat.sub (Nat.succ {kcnt}) (list_length (ListType.nil KExpr))) (Nat.succ {kcnt}) ",
                        "(Eq.trans Nat (Nat.sub (Nat.succ {kcnt}) (list_length (ListType.nil KExpr))) (Nat.sub (Nat.succ {kcnt}) Nat.zero) (Nat.succ {kcnt}) ",
                        "(Eq.cong Nat Nat (fun (y : Nat) => Nat.sub (Nat.succ {kcnt}) y) (list_length (ListType.nil KExpr)) Nat.zero (list_length_nil)) ",
                        "(nat_sub_zero_right (Nat.succ {kcnt})))) ",
                        "h_nil)"
                    ),
                    kcnt = kcnt,
                );
                format!(
                    concat!(
                        "(fun (h_nil : Eq Nat (Nat.sub (Nat.succ {kcnt}) (list_length (ListType.nil KExpr))) Nat.zero) ",
                        "(_happ : Eq (OptionType KExpr) (list_head (list_drop {kcnt} (list_append (ListType.nil KExpr) {cons_a}))) (OptionType.some KExpr major)) => ",
                        "Empty.rec (fun (_ : Empty) => {goal}) ",
                        "(Eq.substType Nat {discr} (Nat.succ {kcnt}) Nat.zero {succ_eq_zero} (Nat.succ {kcnt})))"
                    ),
                    kcnt = kcnt,
                    cons_a = cons_a,
                    goal = goal,
                    discr = discr,
                    succ_eq_zero = succ_eq_zero,
                )
            };

            // zero arm cons case. happ : head (drop 0 ((x::rest)++[a])) = some major.
            //   LHS reduces to some x (append_cons + drop_zero + head_cons), so
            //   some x = some major; goal head (drop 0 (x::rest)) = some x = some major.
            let zero_cons = format!(
                concat!(
                    "(fun (x : KExpr) (rest : ListType KExpr) ",
                    "(_ihc : Eq Nat (Nat.sub (Nat.succ Nat.zero) (list_length rest)) Nat.zero -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop Nat.zero (list_append rest {cons_a}))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop Nat.zero rest)) (OptionType.some KExpr major)) ",
                    "(_h_cons : Eq Nat (Nat.sub (Nat.succ Nat.zero) (list_length (ListType.cons KExpr x rest))) Nat.zero) ",
                    "(happ : Eq (OptionType KExpr) (list_head (list_drop Nat.zero (list_append (ListType.cons KExpr x rest) {cons_a}))) (OptionType.some KExpr major)) => ",
                    // goal: head (drop 0 (x::rest)) = some major.
                    "Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop Nat.zero (ListType.cons KExpr x rest))) ",
                    "(OptionType.some KExpr x) ",
                    "(OptionType.some KExpr major) ",
                    // goal LHS = some x
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop Nat.zero (ListType.cons KExpr x rest))) ",
                    "(list_head (ListType.cons KExpr x rest)) ",
                    "(OptionType.some KExpr x) ",
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_drop Nat.zero (ListType.cons KExpr x rest)) (ListType.cons KExpr x rest) ",
                    "(list_drop_zero (ListType.cons KExpr x rest))) ",
                    "(list_head_cons x rest)) ",
                    // some x = some major, from happ (LHS reduces to some x).
                    "(Eq.trans (OptionType KExpr) (OptionType.some KExpr x) ",
                    "(list_head (list_drop Nat.zero (list_append (ListType.cons KExpr x rest) {cons_a}))) ",
                    "(OptionType.some KExpr major) ",
                    "(Eq.symm (OptionType KExpr) ",
                    "(list_head (list_drop Nat.zero (list_append (ListType.cons KExpr x rest) {cons_a}))) (OptionType.some KExpr x) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop Nat.zero (list_append (ListType.cons KExpr x rest) {cons_a}))) ",
                    "(list_head (list_append (ListType.cons KExpr x rest) {cons_a})) ",
                    "(OptionType.some KExpr x) ",
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_drop Nat.zero (list_append (ListType.cons KExpr x rest) {cons_a})) ",
                    "(list_append (ListType.cons KExpr x rest) {cons_a}) ",
                    "(list_drop_zero (list_append (ListType.cons KExpr x rest) {cons_a}))) ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_append (ListType.cons KExpr x rest) {cons_a})) ",
                    "(list_head (ListType.cons KExpr x (list_append rest {cons_a}))) ",
                    "(OptionType.some KExpr x) ",
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_append (ListType.cons KExpr x rest) {cons_a}) ",
                    "(ListType.cons KExpr x (list_append rest {cons_a})) ",
                    "(list_append_cons x rest {cons_a})) ",
                    "(list_head_cons x (list_append rest {cons_a}))))) ",
                    "happ))"
                ),
                cons_a = cons_a,
            );
            let zero_goal_nil = "Eq (OptionType KExpr) (list_head (list_drop Nat.zero (ListType.nil KExpr))) (OptionType.some KExpr major)".to_string();
            let zero_arm = format!(
                concat!(
                    "(fun (xs0 : ListType KExpr) ",
                    "(h_sub : Eq Nat (Nat.sub (Nat.succ Nat.zero) (list_length xs0)) Nat.zero) ",
                    "(happ : Eq (OptionType KExpr) (list_head (list_drop Nat.zero (list_append xs0 {cons_a}))) (OptionType.some KExpr major)) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq Nat (Nat.sub (Nat.succ Nat.zero) (list_length xs1)) Nat.zero -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop Nat.zero (list_append xs1 {cons_a}))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop Nat.zero xs1)) (OptionType.some KExpr major)) ",
                    "{nil_absurd} ",
                    "{zero_cons} ",
                    "xs0 h_sub happ)"
                ),
                cons_a = cons_a,
                nil_absurd = nil_absurd("Nat.zero", &zero_goal_nil),
                zero_cons = zero_cons,
            );

            // succ arm cons case. m + ih (forall xs0, guard -> happ -> conclusion).
            //   happ : head (drop (succ m)((x::rest)++[a])) = some major
            //        = head (drop m (rest++[a])) = some major   (append_cons + drop_succ + tail_cons)
            //   ih rest (guard_rest) (happ') : head (drop m rest) = some major
            //   goal head (drop (succ m)(x::rest)) = head (drop m rest) = some major.
            let succ_cons = format!(
                concat!(
                    "(fun (x : KExpr) (rest : ListType KExpr) ",
                    "(_ihc : Eq Nat (Nat.sub (Nat.succ (Nat.succ m)) (list_length rest)) Nat.zero -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (list_append rest {cons_a}))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) rest)) (OptionType.some KExpr major)) ",
                    "(h_cons : Eq Nat (Nat.sub (Nat.succ (Nat.succ m)) (list_length (ListType.cons KExpr x rest))) Nat.zero) ",
                    "(happ : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) {cons_a}))) (OptionType.some KExpr major)) => ",
                    // goal: head (drop (succ m)(x::rest)) = some major.
                    "Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop (Nat.succ m) (ListType.cons KExpr x rest))) ",
                    "(list_head (list_drop m rest)) ",
                    "(OptionType.some KExpr major) ",
                    // goal LHS = head (drop m rest)
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_drop (Nat.succ m) (ListType.cons KExpr x rest)) (list_drop m rest) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (ListType.cons KExpr x rest)) ",
                    "(list_drop m (list_tail (ListType.cons KExpr x rest))) ",
                    "(list_drop m rest) ",
                    "(list_drop_succ m (ListType.cons KExpr x rest)) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                    "(list_tail (ListType.cons KExpr x rest)) rest (list_tail_cons x rest)))) ",
                    // head (drop m rest) = some major via ih rest guard_rest happ'
                    "(_ihinner_m rest ",
                    // guard_rest : Nat.sub (succ m) (length rest) = 0, from h_cons.
                    "(Eq.trans Nat (Nat.sub (Nat.succ m) (list_length rest)) ",
                    "(Nat.sub (Nat.succ (Nat.succ m)) (Nat.succ (list_length rest))) Nat.zero ",
                    // sub (succ m)(length rest) = sub (succ(succ m))(succ(length rest))  [symm nat_sub_succ_succ]
                    "(Eq.symm Nat (Nat.sub (Nat.succ (Nat.succ m)) (Nat.succ (list_length rest))) (Nat.sub (Nat.succ m) (list_length rest)) ",
                    "(nat_sub_succ_succ (Nat.succ m) (list_length rest))) ",
                    // = sub (succ(succ m))(length (x::rest)) = 0  [length_cons + h_cons]
                    "(Eq.trans Nat (Nat.sub (Nat.succ (Nat.succ m)) (Nat.succ (list_length rest))) ",
                    "(Nat.sub (Nat.succ (Nat.succ m)) (list_length (ListType.cons KExpr x rest))) Nat.zero ",
                    "(Eq.cong Nat Nat (fun (y : Nat) => Nat.sub (Nat.succ (Nat.succ m)) y) ",
                    "(Nat.succ (list_length rest)) (list_length (ListType.cons KExpr x rest)) ",
                    "(Eq.symm Nat (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) (list_length_cons x rest))) ",
                    "h_cons)) ",
                    // happ' : head (drop m (rest++[a])) = some major, from happ.
                    "(Eq.trans (OptionType KExpr) ",
                    "(list_head (list_drop m (list_append rest {cons_a}))) ",
                    "(list_head (list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) {cons_a}))) ",
                    "(OptionType.some KExpr major) ",
                    // head (drop m (rest++[a])) = head (drop (succ m)((x::rest)++[a])): symm of the unfold.
                    "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                    "(list_drop m (list_append rest {cons_a})) ",
                    "(list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) {cons_a})) ",
                    "(Eq.symm (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) {cons_a})) ",
                    "(list_drop m (list_append rest {cons_a})) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (list_append (ListType.cons KExpr x rest) {cons_a})) ",
                    "(list_drop (Nat.succ m) (ListType.cons KExpr x (list_append rest {cons_a}))) ",
                    "(list_drop m (list_append rest {cons_a})) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop (Nat.succ m) L) ",
                    "(list_append (ListType.cons KExpr x rest) {cons_a}) ",
                    "(ListType.cons KExpr x (list_append rest {cons_a})) ",
                    "(list_append_cons x rest {cons_a})) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_drop (Nat.succ m) (ListType.cons KExpr x (list_append rest {cons_a}))) ",
                    "(list_drop m (list_tail (ListType.cons KExpr x (list_append rest {cons_a})))) ",
                    "(list_drop m (list_append rest {cons_a})) ",
                    "(list_drop_succ m (ListType.cons KExpr x (list_append rest {cons_a}))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop m L) ",
                    "(list_tail (ListType.cons KExpr x (list_append rest {cons_a}))) ",
                    "(list_append rest {cons_a}) ",
                    "(list_tail_cons x (list_append rest {cons_a}))))))) ",
                    "happ)))"
                ),
                cons_a = cons_a,
            );
            let succ_goal_nil = "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (ListType.nil KExpr))) (OptionType.some KExpr major)".to_string();
            let succ_arm = format!(
                concat!(
                    "(fun (m : Nat) ",
                    "(_ihinner_m : forall (xs0 : ListType KExpr), Eq Nat (Nat.sub (Nat.succ m) (list_length xs0)) Nat.zero -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop m (list_append xs0 {cons_a}))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop m xs0)) (OptionType.some KExpr major)) => ",
                    "fun (xs0 : ListType KExpr) ",
                    "(h_sub : Eq Nat (Nat.sub (Nat.succ (Nat.succ m)) (list_length xs0)) Nat.zero) ",
                    "(happ : Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (list_append xs0 {cons_a}))) (OptionType.some KExpr major)) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs1 : ListType KExpr) => Eq Nat (Nat.sub (Nat.succ (Nat.succ m)) (list_length xs1)) Nat.zero -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) (list_append xs1 {cons_a}))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop (Nat.succ m) xs1)) (OptionType.some KExpr major)) ",
                    "{nil_absurd} ",
                    "{succ_cons} ",
                    "xs0 h_sub happ)"
                ),
                cons_a = cons_a,
                nil_absurd = nil_absurd("(Nat.succ m)", &succ_goal_nil),
                succ_cons = succ_cons,
            );

            // Le (succ k)(length xs) -> Nat.sub (succ k)(length xs) = 0.
            let le_to_sub = concat!(
                "(Le.rec (Nat.succ k) (fun (j : Nat) (_ : Le (Nat.succ k) j) => Eq Nat (Nat.sub (Nat.succ k) j) Nat.zero) ",
                "(nat_sub_self (Nat.succ k)) ",
                "(fun (m : Nat) (_h : Le (Nat.succ k) m) (ihm : Eq Nat (Nat.sub (Nat.succ k) m) Nat.zero) => ",
                "Eq.trans Nat (Nat.sub (Nat.succ k) (Nat.succ m)) (Nat.pred (Nat.sub (Nat.succ k) m)) Nat.zero ",
                "(Eq.refl Nat (Nat.pred (Nat.sub (Nat.succ k) m))) ",
                "(Eq.trans Nat (Nat.pred (Nat.sub (Nat.succ k) m)) (Nat.pred Nat.zero) Nat.zero ",
                "(Eq.cong Nat Nat Nat.pred (Nat.sub (Nat.succ k) m) Nat.zero ihm) (Eq.refl Nat Nat.zero))) ",
                "(list_length xs) hle)"
            );

            let value = format!(
                concat!(
                    "fun (k : Nat) (xs : ListType KExpr) (a : KExpr) (major : KExpr) ",
                    "(hle : Le (Nat.succ k) (list_length xs)) ",
                    "(happ : Eq (OptionType KExpr) (list_head (list_drop k (list_append xs {cons_a}))) (OptionType.some KExpr major)) => ",
                    "(fun (hsub : Eq Nat (Nat.sub (Nat.succ k) (list_length xs)) Nat.zero) => ",
                    "Nat.rec ",
                    "(fun (k0 : Nat) => forall (xs0 : ListType KExpr), Eq Nat (Nat.sub (Nat.succ k0) (list_length xs0)) Nat.zero -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop k0 (list_append xs0 {cons_a}))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop k0 xs0)) (OptionType.some KExpr major)) ",
                    "{zero_arm} ",
                    "{succ_arm} ",
                    "k xs hsub happ) ",
                    "{le_to_sub}"
                ),
                cons_a = cons_a,
                zero_arm = zero_arm,
                succ_arm = succ_arm,
                le_to_sub = le_to_sub,
            );

            self.add_definition(SpecDefinition {
                name: "list_head_drop_append_some_inv".to_string(),
                type_src: concat!(
                    "forall (k : Nat) (xs : ListType KExpr) (a : KExpr) (major : KExpr), ",
                    "Le (Nat.succ k) (list_length xs) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop k (list_append xs (ListType.cons KExpr a (ListType.nil KExpr))))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop k xs)) (OptionType.some KExpr major)"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "Converse major-premise stability: if the drop window lies STRICTLY inside xs (Le (succ k) (length xs)) and head (drop k (xs ++ [a])) = some major, then head (drop k xs) = some major already — the appended [a] never reached the window. The strict guard is essential (at k = length xs the appended a IS the major and the un-appended head is none). Le.rec collapses the guard to Nat.sub (succ k)(length xs) = 0; Nat.rec on k carries that strict guard / ListType.rec on xs kills the nil corner via Empty.rec. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "list_head".to_string(),
                    "list_drop".to_string(),
                    "list_append".to_string(),
                    "list_length".to_string(),
                    "list_tail".to_string(),
                    "Nat.rec".to_string(),
                    "Nat.pred".to_string(),
                    "Nat.sub".to_string(),
                    "ListType.rec".to_string(),
                    "Le".to_string(),
                    "Le.rec".to_string(),
                    "Empty.rec".to_string(),
                    "Eq.substType".to_string(),
                    "nat_sub_self".to_string(),
                    "nat_sub_zero_right".to_string(),
                    "nat_sub_succ_succ".to_string(),
                    "list_drop_zero".to_string(),
                    "list_drop_succ".to_string(),
                    "list_tail_cons".to_string(),
                    "list_append_cons".to_string(),
                    "list_head_cons".to_string(),
                    "list_length_cons".to_string(),
                    "list_length_nil".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_reduct_app_inner (#2859 (iota,app) minimal join — the CONVERSE of
        // iota_reduct_app_over): if (app f a) is an over-applied iota redex
        // (iota_reduct env (app f a) = some e1) and the recovered major window lies
        // STRICTLY inside kapp_args f (the window continuation hwin), then f itself
        // is a redex: CPS-deliver some f1 with iota_reduct env f = some f1. Inverts
        // iota_reduct env (app f a) via iota_reduct_some_inv (recovering recname /
        // meta / major / cname / rule + h1..h5); since kapp_fn (app f a) = kapp_fn f
        // (kapp_fn_app) the head lookups (h1, h4, h5) transfer verbatim, and since
        // kapp_args (app f a) = kapp_args f ++ [a] (kapp_args_app) with the major
        // window STRICTLY inside kapp_args f (hwin), the major lookup over kapp_args
        // f recovers via list_head_drop_append_some_inv (#D.2). Rebuilds
        // iota_reduct env f via opt_bind_some_intro 5x; the reduct slot is the bare
        // reduct over kapp_args f (= the delivered f1, so L6 is Eq.refl). The
        // over-application hypothesis h5r is unused (the converse rebuild of
        // iota_reduct env f is independent of e1).
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            // major_idx / prefix over a metavariable m0 (for hwin's continuation type).
            let major_idx_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m})) (recmeta_num_indices {m}))")
            };
            let len_f = "(list_length (kapp_args f))";

            // the bare reduct over kapp_args f / kapp_args major (= delivered f1).
            let reduct_f = format!(
                "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args f)) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
                 (apply_spine (list_take {prefix_n} (kapp_args f)) {p_rhs})))"
            );

            // iota_reduct env f opt_bind continuations (the def, with e := f), L6..L2.
            let lf6 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct_f})");
            let lf5 = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {lf6})"
            );
            let lf4 = format!(
                "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {lf5})"
            );
            let lf3 = format!("(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args f))) {lf4})");
            let lf2 = format!(
                "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {lf3})"
            );

            // The reduct over kapp_args (app f a) (as recovered in h5r of the inversion).
            let reduct_app = format!(
                "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args (KExpr.app f a))) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
                 (apply_spine (list_take {prefix_n} (kapp_args (KExpr.app f a))) {p_rhs})))"
            );

            // h1 transferred to f: kexpr_const_name (kapp_fn f) = some recname.
            let h1f = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn (KExpr.app f a)) (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";

            // h3 transferred to (kapp_args f ++ [a]): head (drop major_idx (kapp_args f ++ [a])) = some major.
            let h3_app = format!(
                "(Eq.trans (OptionType KExpr) \
                 (list_head (list_drop {major_idx} (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))))) \
                 (list_head (list_drop {major_idx} (kapp_args (KExpr.app f a)))) \
                 (OptionType.some KExpr major) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop {major_idx} L)) \
                 (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args (KExpr.app f a)) \
                 (Eq.symm (ListType KExpr) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a))) \
                 h3)"
            );

            // h3 recovered over kapp_args f (the converse, via list_head_drop_append_some_inv + hwin).
            let h3f = format!(
                "(list_head_drop_append_some_inv {major_idx} (kapp_args f) a major \
                 (hwin recname meta {h1f} h2) {h3_app})"
            );

            // The rebuild of iota_reduct env f = some (reduct over f), 5x opt_bind_some_intro.
            let recon = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn f)) {lf2} recname {reduct_f} {h1f} \
                 (opt_bind_some_intro RecMeta KExpr (recmeta_for env recname) {lf3} meta {reduct_f} h2 \
                 (opt_bind_some_intro KExpr KExpr (list_head (list_drop {major_idx} (kapp_args f))) {lf4} major {reduct_f} {h3f} \
                 (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn major)) {lf5} cname {reduct_f} h4 \
                 (opt_bind_some_intro RecRule KExpr (recrule_for env recname cname) {lf6} rule {reduct_f} h5 \
                 (Eq.refl (OptionType KExpr) (OptionType.some KExpr {reduct_f})))))))"
            );

            // The continuation k passed to iota_reduct_some_inv (binders match kont
            // for (app f a)). We deliver f1 := reduct over f to the OUTER continuation kc.
            let kont_lambda = format!(
                "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1)) => \
                 kc {reduct_f} ({recon}))"
            );

            let value = format!(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) \
                 (hwin : (forall (rn : Name) (m0 : RecMeta), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) -> \
                 Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0) -> \
                 Le (Nat.succ {major_idx_m0}) {len_f})) \
                 (h : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
                 (C : Prop) \
                 (kc : (forall (f1 : KExpr), Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> C)) => \
                 iota_reduct_some_inv env (KExpr.app f a) e1 C h {kont_lambda}",
                major_idx_m0 = major_idx_of("m0"),
                len_f = len_f,
                kont_lambda = kont_lambda,
            );

            let type_src = format!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr), \
                 (forall (rn : Name) (m0 : RecMeta), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) -> \
                 Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0) -> \
                 Le (Nat.succ {major_idx_m0}) {len_f}) -> \
                 Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> \
                 forall (C : Prop), (forall (f1 : KExpr), Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> C) -> C",
                major_idx_m0 = major_idx_of("m0"),
                len_f = len_f,
            );

            self.add_definition(SpecDefinition {
                name: "iota_reduct_app_inner".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "Converse over-application identity for iota (the (a)-join CONVERSE of iota_reduct_app_over): if iota_reduct env (app f a) = some e1 and the recovered major window lies STRICTLY inside kapp_args f (the hwin continuation: Le (succ major_idx(m0)) (length (kapp_args f))), then f itself is a redex — CPS-deliver some f1 with iota_reduct env f = some f1. Inverts iota_reduct env (app f a) via iota_reduct_some_inv; the head lookups transfer verbatim (kapp_fn_app), the major lookup over kapp_args f recovers via list_head_drop_append_some_inv from h3 over kapp_args f ++ [a] (kapp_args_app) + hwin. Rebuilds via opt_bind_some_intro x5 (the reduct slot is the bare reduct over kapp_args f, = the delivered f1, so L6 is Eq.refl). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "list_head_drop_append_some_inv".to_string(),
                    "kapp_args_app".to_string(),
                    "kapp_fn_app".to_string(),
                    "Le".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // nat_le_succ_or (#2859 (iota,app) minimal join — the antisymmetry the
        // boundary identity needs): Le m n is exactly "m = n or m < n". CPS form
        // (no sum type in the fragment): deliver to two continuations keq (Eq m n)
        // and klt (Le (succ m) n). Le.rec on the proof (m promoted to parameter,
        // motive over the second index j): refl arm (j = m) calls keq (Eq.refl m);
        // step arm (j = succ p from Le m p) calls klt (le_succ_succ m p _h).
        self.add_definition(SpecDefinition {
            name: "nat_le_succ_or".to_string(),
            type_src: concat!(
                "forall (m : Nat) (n : Nat), Le m n -> ",
                "forall (C : Prop), (Eq Nat m n -> C) -> (Le (Nat.succ m) n -> C) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (m : Nat) (n : Nat) (h : Le m n) => ",
                    "Le.rec m ",
                    "(fun (j : Nat) (_ : Le m j) => forall (C : Prop), (Eq Nat m j -> C) -> (Le (Nat.succ m) j -> C) -> C) ",
                    // refl arm (j = m)
                    "(fun (C : Prop) (keq : Eq Nat m m -> C) (_klt : Le (Nat.succ m) m -> C) => keq (Eq.refl Nat m)) ",
                    // step arm (j = succ p, _hp : Le m p)
                    "(fun (p : Nat) (_hp : Le m p) (_ihp : forall (C : Prop), (Eq Nat m p -> C) -> (Le (Nat.succ m) p -> C) -> C) => ",
                    "fun (C : Prop) (_keq : Eq Nat m (Nat.succ p) -> C) (klt : Le (Nat.succ m) (Nat.succ p) -> C) => ",
                    "klt (le_succ_succ m p _hp)) ",
                    "n h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le m n is exactly m = n or m < n (CPS, no sum type): Le m n -> forall C, (Eq m n -> C) -> (Le (succ m) n -> C) -> C. Le.rec on the proof (m parameter, motive over the 2nd index): refl arm delivers keq (Eq.refl), step arm delivers klt (le_succ_succ). The case-split the boundary identity needs to discharge the major-index trichotomy. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.rec".to_string(),
                "le_succ_succ".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // le_succ_le_pred (#2859 (iota,app) minimal join): Le (succ a) c -> Le a
        // (Nat.pred c). Le.rec on the proof (succ a parameter, motive Le a
        // (Nat.pred j)): refl arm (j = succ a) is Le a (pred (succ a)) = Le a a via
        // Le.refl; step arm (j = succ p from _hp : Le (succ a) p) is Le a (pred
        // (succ p)) = Le a p, obtained from _hp directly by dropping the left succ
        // (le_trans a (succ a) p (Le.step ..) _hp) — the IH is unused. Nat.pred
        // reduces on succ.
        self.add_definition(SpecDefinition {
            name: "le_succ_le_pred".to_string(),
            type_src: "forall (a : Nat) (c : Nat), Le (Nat.succ a) c -> Le a (Nat.pred c)"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (c : Nat) (h : Le (Nat.succ a) c) => ",
                    "Le.rec (Nat.succ a) (fun (j : Nat) (_ : Le (Nat.succ a) j) => Le a (Nat.pred j)) ",
                    // refl: Le a (pred (succ a)) = Le a a
                    "(Le.refl a) ",
                    // step: Le a (pred (succ p)) = Le a p, from _hp by dropping left succ.
                    "(fun (p : Nat) (_hp : Le (Nat.succ a) p) (_ihp : Le a (Nat.pred p)) => ",
                    "le_trans a (Nat.succ a) p (Le.step a a (Le.refl a)) _hp) ",
                    "c h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le (succ a) c -> Le a (Nat.pred c). Le.rec on the proof (succ a parameter, motive Le a (Nat.pred j)): refl arm via Le.refl (pred (succ a) reduces to a); step arm drops the left succ from _hp via le_trans + Le.step (IH unused). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "Le.refl".to_string(),
                "Le.step".to_string(),
                "Le.rec".to_string(),
                "le_trans".to_string(),
                "Nat.pred".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // le_pred_pred (#2859 (iota,app) minimal join): Le (succ a) (succ b) -> Le
        // a b. Specialize le_succ_le_pred at c := succ b: Le (succ a)(succ b) -> Le
        // a (Nat.pred (succ b)), and Nat.pred (succ b) reduces to b so the result
        // is Le a b definitionally.
        self.add_definition(SpecDefinition {
            name: "le_pred_pred".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Le (Nat.succ a) (Nat.succ b) -> Le a b"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (h : Le (Nat.succ a) (Nat.succ b)) => ",
                    "le_succ_le_pred a (Nat.succ b) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Le (succ a) (succ b) -> Le a b. Specialize le_succ_le_pred at c := succ b; Nat.pred (succ b) reduces to b. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Le".to_string(),
                "le_succ_le_pred".to_string(),
                "Nat.pred".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // list_length_append_singleton (#2859 (iota,app) minimal join): appending a
        // singleton bumps the length by one: length (xs ++ [a]) = succ (length xs).
        // ListType.rec on xs: nil via list_append_nil + list_length_nil (both
        // reduce); cons peels via list_append_cons + list_length_cons onto the IH.
        {
            let cons_a = "(ListType.cons KExpr a (ListType.nil KExpr))";
            let goal_for = |xs: &str| -> String {
                format!(
                    "Eq Nat (list_length (list_append {xs} {cons_a})) (Nat.succ (list_length {xs}))"
                )
            };
            // nil arm: length (nil ++ [a]) = length [a] = succ 0 = succ (length nil).
            let nil_arm = format!(
                "(Eq.trans Nat \
                 (list_length (list_append (ListType.nil KExpr) {cons_a})) \
                 (list_length {cons_a}) \
                 (Nat.succ (list_length (ListType.nil KExpr))) \
                 (Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) \
                 (list_append (ListType.nil KExpr) {cons_a}) {cons_a} (list_append_nil {cons_a})) \
                 (Eq.trans Nat \
                 (list_length {cons_a}) \
                 (Nat.succ (list_length (ListType.nil KExpr))) \
                 (Nat.succ (list_length (ListType.nil KExpr))) \
                 (list_length_cons a (ListType.nil KExpr)) \
                 (Eq.refl Nat (Nat.succ (list_length (ListType.nil KExpr))))))"
            );
            // cons arm: x rest ih (ih = goal_for rest).
            //   length ((x::rest)++[a]) = length (x::(rest++[a]))  [append_cons]
            //     = succ (length (rest++[a]))                       [length_cons]
            //     = succ (succ (length rest))                       [ih]
            //   RHS succ (length (x::rest)) = succ (succ (length rest))  [length_cons]
            let ih_ty = goal_for("rest");
            // cons lands at succ (succ (length rest)); the motive RHS is
            // succ (length (x::rest)); close the last gap with length_cons.
            let cons_arm = format!(
                "(fun (x : KExpr) (rest : ListType KExpr) (ih : {ih_ty}) => \
                 Eq.trans Nat \
                 (list_length (list_append (ListType.cons KExpr x rest) {cons_a})) \
                 (Nat.succ (Nat.succ (list_length rest))) \
                 (Nat.succ (list_length (ListType.cons KExpr x rest))) \
                 (Eq.trans Nat \
                 (list_length (list_append (ListType.cons KExpr x rest) {cons_a})) \
                 (Nat.succ (list_length (list_append rest {cons_a}))) \
                 (Nat.succ (Nat.succ (list_length rest))) \
                 (Eq.trans Nat \
                 (list_length (list_append (ListType.cons KExpr x rest) {cons_a})) \
                 (list_length (ListType.cons KExpr x (list_append rest {cons_a}))) \
                 (Nat.succ (list_length (list_append rest {cons_a}))) \
                 (Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) \
                 (list_append (ListType.cons KExpr x rest) {cons_a}) \
                 (ListType.cons KExpr x (list_append rest {cons_a})) \
                 (list_append_cons x rest {cons_a})) \
                 (list_length_cons x (list_append rest {cons_a}))) \
                 (Eq.cong Nat Nat (fun (N : Nat) => Nat.succ N) \
                 (list_length (list_append rest {cons_a})) (Nat.succ (list_length rest)) ih)) \
                 (Eq.cong Nat Nat (fun (N : Nat) => Nat.succ N) \
                 (Nat.succ (list_length rest)) (list_length (ListType.cons KExpr x rest)) \
                 (Eq.symm Nat (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest)) (list_length_cons x rest))))",
            );
            let value = format!(
                "fun (xs : ListType KExpr) (a : KExpr) => \
                 ListType.rec KExpr \
                 (fun (xs0 : ListType KExpr) => {goal0}) \
                 {nil_arm} \
                 {cons_arm} \
                 xs",
                goal0 = goal_for("xs0"),
                nil_arm = nil_arm,
                cons_arm = cons_arm,
            );
            self.add_definition(SpecDefinition {
                name: "list_length_append_singleton".to_string(),
                type_src: format!(
                    "forall (xs : ListType KExpr) (a : KExpr), {}",
                    goal_for("xs")
                ),
                value_src: Some(value),
                is_axiom: false,
                description: "Appending a singleton bumps length by one: length (xs ++ [a]) = succ (length xs). ListType.rec on xs (nil via list_append_nil + list_length_nil; cons via list_append_cons + list_length_cons onto the IH). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "list_length".to_string(),
                    "list_append".to_string(),
                    "ListType.rec".to_string(),
                    "list_append_nil".to_string(),
                    "list_append_cons".to_string(),
                    "list_length_nil".to_string(),
                    "list_length_cons".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_reduct_app_minimal_boundary (#2859 (iota,app) minimal join — THE
        // PAYOFF): when (app f a) is an iota redex but f is NOT (iota_reduct env f =
        // none), the redex's major premise sits at the BOUNDARY and IS the appended
        // arg a. CPS-deliver the inversion witnesses of iota_reduct env (app f a) =
        // some e1 together with the boundary identity Eq KExpr major a. Inverts via
        // iota_reduct_some_inv (recovering meta + h3: head (drop major_idx (kapp_args
        // (app f a))) = some major); list_head_drop_some_le_succ on h3 gives Le (succ
        // major_idx) (length (kapp_args (app f a))) = Le (succ major_idx) (succ
        // (length (kapp_args f))) [list_length_append_singleton], whence Le major_idx
        // (length (kapp_args f)) [le_pred_pred]. nat_le_succ_or splits this: the
        // STRICT arm (Le (succ major_idx)(length kapp_args f)) is impossible — it
        // satisfies iota_reduct_app_inner's window, forcing iota_reduct env f = some
        // _, contradicting the none hypothesis (option_none_ne_some); the EQUAL arm
        // (major_idx = length kapp_args f) locates the major at the boundary, so
        // h3 + list_head_drop_len_append give some major = some a, i.e. major = a
        // (option_some_inj).
        {
            let major_idx_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m})) (recmeta_num_indices {m}))")
            };
            let prefix_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m}))")
            };
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            let major_idx = major_idx_of("meta");
            let prefix_n = prefix_of("meta");
            let len_f = "(list_length (kapp_args f))";
            let kargs_app = "(kapp_args (KExpr.app f a))";
            let kargs_f_snoc =
                "(list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))";

            // h3 type as recovered by iota_reduct_some_inv (over app f a).
            let h3_type = format!(
                "Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major)"
            );
            // The reduct over kapp_args (app f a), as recovered in h5r.
            let reduct_app = format!(
                "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_app}) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
                 (apply_spine (list_take {prefix_n} {kargs_app}) {p_rhs})))"
            );

            // The CPS continuation type k delivered to (binds the inversion witnesses
            // over (app f a) + the boundary identity Eq KExpr major a).
            let k_type = format!(
                "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) -> \
                 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
                 Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major) -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1) -> \
                 Eq KExpr major a -> C)"
            );

            // Le (succ major_idx) (length (kapp_args (app f a))) from h3.
            let hlt_app = format!("(list_head_drop_some_le_succ {major_idx} {kargs_app} major h3)");
            // length (kapp_args (app f a)) = succ (length (kapp_args f)):
            //   kapp_args_app then list_length_append_singleton.
            let len_app_eq = format!(
                "(Eq.trans Nat (list_length {kargs_app}) (list_length {kargs_f_snoc}) (Nat.succ {len_f}) \
                 (Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) \
                 {kargs_app} {kargs_f_snoc} (kapp_args_app f a)) \
                 (list_length_append_singleton (kapp_args f) a))"
            );
            // Le (succ major_idx) (succ (length (kapp_args f))), by transporting hlt_app.
            let hlt_succ = format!(
                "(Eq.subst Nat (fun (z : Nat) => Le (Nat.succ {major_idx}) z) \
                 (list_length {kargs_app}) (Nat.succ {len_f}) {len_app_eq} {hlt_app})"
            );
            // Le major_idx (length (kapp_args f)) via le_pred_pred.
            let hle = format!("(le_pred_pred {major_idx} {len_f} {hlt_succ})");

            // --- EQUAL arm: heq : Eq major_idx (length kapp_args f) -> major = a -> k ... ---
            // From h3 (over major_idx) rewrite major_idx -> length kapp_args f and
            // kapp_args (app f a) -> kapp_args f ++ [a]; list_head_drop_len_append
            // gives head (...) = some a; combine to major = a via option_some_inj.
            // h3 over (kapp_args f ++ [a]) at index major_idx:
            let h3_snoc = format!(
                "(Eq.trans (OptionType KExpr) \
                 (list_head (list_drop {major_idx} {kargs_f_snoc})) \
                 (list_head (list_drop {major_idx} {kargs_app})) \
                 (OptionType.some KExpr major) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop {major_idx} L)) \
                 {kargs_f_snoc} {kargs_app} \
                 (Eq.symm (ListType KExpr) {kargs_app} {kargs_f_snoc} (kapp_args_app f a))) \
                 h3)"
            );
            // some a = some major : rewrite list_head_drop_len_append's index
            // (length kapp_args f) to major_idx (symm heq), landing on h3_snoc.
            let some_a_eq_some_major = format!(
                "(Eq.trans (OptionType KExpr) \
                 (OptionType.some KExpr a) \
                 (list_head (list_drop {major_idx} {kargs_f_snoc})) \
                 (OptionType.some KExpr major) \
                 (Eq.subst Nat (fun (z : Nat) => Eq (OptionType KExpr) (OptionType.some KExpr a) (list_head (list_drop z {kargs_f_snoc}))) \
                 {len_f} {major_idx} \
                 (Eq.symm Nat {major_idx} {len_f} heq) \
                 (Eq.symm (OptionType KExpr) (list_head (list_drop {len_f} {kargs_f_snoc})) (OptionType.some KExpr a) \
                 (list_head_drop_len_append (kapp_args f) a))) \
                 {h3_snoc})"
            );
            // major = a : option_some_inj on (symm some_a_eq_some_major) : some major = some a.
            let major_eq_a = format!(
                "(option_some_inj KExpr major a \
                 (Eq.symm (OptionType KExpr) (OptionType.some KExpr a) (OptionType.some KExpr major) {some_a_eq_some_major}))"
            );
            let keq_arm = format!(
                "(fun (heq : Eq Nat {major_idx} {len_f}) => \
                 k recname meta major cname rule h1 h2 h3 h4 h5 h5r {major_eq_a})"
            );

            // --- STRICT arm: hstrict : Le (succ major_idx)(length kapp_args f) -> absurd. ---
            // Build hwin (forall rn m0, head=some rn -> recmeta=some m0 -> Le (succ
            // major_idx(m0)) len) by unifying (rn,m0) with (recname,meta) via
            // option_some_inj, exactly as iota_reduct_app_some; then iota_reduct_app_inner
            // forces iota_reduct env f = some f1, contradicting hnone.
            let h1f = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn (KExpr.app f a)) (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";
            // hrn : Eq Name recname rn from h1f (head f = some recname) and h1' (head f = some rn).
            let hrn = format!(
                "(option_some_inj Name recname rn \
                 (Eq.trans (OptionType Name) (OptionType.some Name recname) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) \
                 (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname) {h1f}) h1'))"
            );
            // h2recname : recmeta_for env recname = some m0, from h2' over rn along rn=recname.
            let h2recname = format!(
                "(Eq.substType Name (fun (n : Name) => Eq (OptionType RecMeta) (recmeta_for env n) (OptionType.some RecMeta m0)) rn recname \
                 (Eq.symm Name recname rn {hrn}) h2')"
            );
            // meta = m0 from h2 (recmeta_for env recname = some meta) + h2recname.
            let meta_eq_m0 = format!(
                "(option_some_inj RecMeta meta m0 \
                 (Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta) (recmeta_for env recname) (OptionType.some RecMeta m0) \
                 (Eq.symm (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) h2) {h2recname}))"
            );
            // hwin continuation: Le (succ major_idx(m0)) len, by transporting hstrict
            // (over meta) along meta = m0.
            let hwin = format!(
                "(fun (rn : Name) (m0 : RecMeta) \
                 (h1' : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn)) \
                 (h2' : Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0)) => \
                 Eq.substType RecMeta (fun (mm : RecMeta) => Le (Nat.succ {major_idx_mm}) {len_f}) meta m0 \
                 {meta_eq_m0} \
                 hstrict)",
                major_idx_mm = major_idx_of("mm"),
            );
            // iota_reduct_app_inner forces some f1; contradict hnone.
            let strict_arm = format!(
                "(fun (hstrict : Le (Nat.succ {major_idx}) {len_f}) => \
                 iota_reduct_app_inner env f a e1 {hwin} hsome C \
                 (fun (f1 : KExpr) (hf1 : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => \
                 option_none_ne_some KExpr f1 C \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct env f) (OptionType.some KExpr f1) \
                 (Eq.symm (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) hnone) hf1)))"
            );

            let value = format!(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) \
                 (hsome : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
                 (hnone : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
                 (C : Prop) (k : {k_type}) => \
                 iota_reduct_some_inv env (KExpr.app f a) e1 C hsome \
                 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : {h3_type}) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1)) => \
                 nat_le_succ_or {major_idx} {len_f} {hle} C \
                 {keq_arm} \
                 {strict_arm})",
                k_type = k_type,
                h3_type = h3_type,
                reduct_app = reduct_app,
                major_idx = major_idx,
                len_f = len_f,
                hle = hle,
                keq_arm = keq_arm,
                strict_arm = strict_arm,
            );

            let type_src = format!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr), \
                 Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> \
                 Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> \
                 forall (C : Prop), {k_type} -> C",
                k_type = k_type,
            );

            self.add_definition(SpecDefinition {
                name: "iota_reduct_app_minimal_boundary".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "The (a)-join PAYOFF: when (app f a) is an iota redex but f is not (iota_reduct env f = none), the redex's major premise sits at the boundary and IS the appended arg a. CPS-delivers the inversion witnesses of iota_reduct env (app f a) = some e1 plus the boundary identity Eq KExpr major a. list_head_drop_some_le_succ on h3 + list_length_append_singleton + le_pred_pred give Le major_idx (length kapp_args f); nat_le_succ_or splits it: the strict arm is killed via iota_reduct_app_inner (would force iota_reduct env f = some _, against hnone, via option_none_ne_some); the equal arm locates the major at the boundary, so h3 + list_head_drop_len_append + option_some_inj give major = a. DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "iota_reduct_app_inner".to_string(),
                    "list_head_drop_some_le_succ".to_string(),
                    "list_head_drop_len_append".to_string(),
                    "list_length_append_singleton".to_string(),
                    "le_pred_pred".to_string(),
                    "nat_le_succ_or".to_string(),
                    "kapp_args_app".to_string(),
                    "kapp_fn_app".to_string(),
                    "option_some_inj".to_string(),
                    "option_none_ne_some".to_string(),
                    "Le".to_string(),
                    "Eq.subst".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_app_major_not_rec — discharge of the (a) minimal join's residual
        // side-condition (iota_reduct env a = none) from the env's constructor/
        // recursor-disjointness interface (RecEnvCtorRecDisjoint). When (app f a) is
        // an iota redex (=> e1) but f is not (iota_reduct env f = none), the boundary
        // lemma locates the redex's major premise AT the appended arg a (major = a)
        // and delivers the constructor-head witness (head major = some cname) and the
        // rule witness (recrule_for env recname cname = some rule). The disjointness
        // projector turns those into iota_reduct env major = none; transport along
        // major = a yields iota_reduct env a = none. This is the fact that was carried
        // as the conditional hypothesis hmaj_nr in par_strips_c_iota_app_full — now
        // discharged internally from the faithful interface.
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            let kargs_app = "(kapp_args (KExpr.app f a))";
            let reduct_app = format!(
                "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_app}) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
                 (apply_spine (list_take {prefix_n} {kargs_app}) {p_rhs})))"
            );
            let value = format!(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) \
                 (disjoint : RecEnvCtorRecDisjoint env) \
                 (hsome : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
                 (hfnone : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) => \
                 iota_reduct_app_minimal_boundary env f a e1 hsome hfnone \
                 (Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)) \
                 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1)) \
                 (hbnd : Eq KExpr major a) => \
                 Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType KExpr) (iota_reduct env x) (OptionType.none KExpr)) \
                 major a hbnd \
                 (recenv_ctor_rec_disjoint_major env recname cname rule major disjoint h4 h5))"
            );
            self.add_definition(SpecDefinition {
                name: "iota_app_major_not_rec".to_string(),
                type_src: concat!(
                    "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr), ",
                    "RecEnvCtorRecDisjoint env -> ",
                    "Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> ",
                    "Eq (OptionType KExpr) (iota_reduct env a) (OptionType.none KExpr)"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "Discharges the (a) minimal (iota,app) join's residual side-condition from the env's constructor/recursor-disjointness interface: when (app f a) is an iota redex (=> e1) but f is not (iota_reduct env f = none), iota_reduct_app_minimal_boundary locates the major premise at the appended arg a (major = a) and delivers the constructor-head witness + rule witness, which recenv_ctor_rec_disjoint_major turns into iota_reduct env major = none; transport along major = a gives iota_reduct env a = none. This is the fact carried as the conditional hypothesis hmaj_nr in par_strips_c_iota_app_full, now discharged internally from RecEnvCtorRecDisjoint. DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_app_minimal_boundary".to_string(),
                    "RecEnvCtorRecDisjoint".to_string(),
                    "recenv_ctor_rec_disjoint_major".to_string(),
                    "kexpr_const_name".to_string(),
                    "kapp_fn".to_string(),
                    "Eq.subst".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // D.1b — iota_reduct_app_minimal_boundary_idx (#2859 (iota,app) minimal
        // join): the boundary lemma AUGMENTED to also deliver the index identity
        // Eq Nat major_idx (length (kapp_args f)). Verbatim copy of
        // iota_reduct_app_minimal_boundary except the EQUAL arm additionally passes
        // heq (the index equation) to the continuation. The par-reduction
        // reconstruction (iota_reduct_par_app_redex, D.2) consumes BOTH major = a
        // and major_idx = length(kapp_args f) to locate the major at the boundary of
        // the reduced spine kapp_args f' (= same length, so still at the boundary).
        {
            let major_idx_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m})) (recmeta_num_indices {m}))")
            };
            let prefix_of = |m: &str| -> String {
                format!("(Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m}))")
            };
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            let major_idx = major_idx_of("meta");
            let prefix_n = prefix_of("meta");
            let len_f = "(list_length (kapp_args f))";
            let kargs_app = "(kapp_args (KExpr.app f a))";
            let kargs_f_snoc =
                "(list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))";

            let h3_type = format!(
                "Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major)"
            );
            let reduct_app = format!(
                "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_app}) \
                 (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
                 (apply_spine (list_take {prefix_n} {kargs_app}) {p_rhs})))"
            );

            // The CPS continuation type — like the boundary lemma's, but with the
            // EXTRA index identity Eq Nat major_idx (length (kapp_args f)).
            let k_type = format!(
                "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) -> \
                 Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
                 Eq (OptionType KExpr) (list_head (list_drop {major_idx} {kargs_app})) (OptionType.some KExpr major) -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1) -> \
                 Eq KExpr major a -> Eq Nat {major_idx} {len_f} -> C)"
            );

            let hlt_app = format!("(list_head_drop_some_le_succ {major_idx} {kargs_app} major h3)");
            let len_app_eq = format!(
                "(Eq.trans Nat (list_length {kargs_app}) (list_length {kargs_f_snoc}) (Nat.succ {len_f}) \
                 (Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) \
                 {kargs_app} {kargs_f_snoc} (kapp_args_app f a)) \
                 (list_length_append_singleton (kapp_args f) a))"
            );
            let hlt_succ = format!(
                "(Eq.subst Nat (fun (z : Nat) => Le (Nat.succ {major_idx}) z) \
                 (list_length {kargs_app}) (Nat.succ {len_f}) {len_app_eq} {hlt_app})"
            );
            let hle = format!("(le_pred_pred {major_idx} {len_f} {hlt_succ})");

            // EQUAL arm: derive major = a (as in the boundary lemma) AND pass heq.
            let h3_snoc = format!(
                "(Eq.trans (OptionType KExpr) \
                 (list_head (list_drop {major_idx} {kargs_f_snoc})) \
                 (list_head (list_drop {major_idx} {kargs_app})) \
                 (OptionType.some KExpr major) \
                 (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop {major_idx} L)) \
                 {kargs_f_snoc} {kargs_app} \
                 (Eq.symm (ListType KExpr) {kargs_app} {kargs_f_snoc} (kapp_args_app f a))) \
                 h3)"
            );
            let some_a_eq_some_major = format!(
                "(Eq.trans (OptionType KExpr) \
                 (OptionType.some KExpr a) \
                 (list_head (list_drop {major_idx} {kargs_f_snoc})) \
                 (OptionType.some KExpr major) \
                 (Eq.subst Nat (fun (z : Nat) => Eq (OptionType KExpr) (OptionType.some KExpr a) (list_head (list_drop z {kargs_f_snoc}))) \
                 {len_f} {major_idx} \
                 (Eq.symm Nat {major_idx} {len_f} heq) \
                 (Eq.symm (OptionType KExpr) (list_head (list_drop {len_f} {kargs_f_snoc})) (OptionType.some KExpr a) \
                 (list_head_drop_len_append (kapp_args f) a))) \
                 {h3_snoc})"
            );
            let major_eq_a = format!(
                "(option_some_inj KExpr major a \
                 (Eq.symm (OptionType KExpr) (OptionType.some KExpr a) (OptionType.some KExpr major) {some_a_eq_some_major}))"
            );
            let keq_arm = format!(
                "(fun (heq : Eq Nat {major_idx} {len_f}) => \
                 k recname meta major cname rule h1 h2 h3 h4 h5 h5r {major_eq_a} heq)"
            );

            // STRICT arm: killed by hnone via iota_reduct_app_inner (identical to the
            // boundary lemma).
            let h1f = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn (KExpr.app f a)) (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";
            let hrn = format!(
                "(option_some_inj Name recname rn \
                 (Eq.trans (OptionType Name) (OptionType.some Name recname) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn) \
                 (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname) {h1f}) h1'))"
            );
            let h2recname = format!(
                "(Eq.substType Name (fun (n : Name) => Eq (OptionType RecMeta) (recmeta_for env n) (OptionType.some RecMeta m0)) rn recname \
                 (Eq.symm Name recname rn {hrn}) h2')"
            );
            let meta_eq_m0 = format!(
                "(option_some_inj RecMeta meta m0 \
                 (Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta) (recmeta_for env recname) (OptionType.some RecMeta m0) \
                 (Eq.symm (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) h2) {h2recname}))"
            );
            let hwin = format!(
                "(fun (rn : Name) (m0 : RecMeta) \
                 (h1' : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name rn)) \
                 (h2' : Eq (OptionType RecMeta) (recmeta_for env rn) (OptionType.some RecMeta m0)) => \
                 Eq.substType RecMeta (fun (mm : RecMeta) => Le (Nat.succ {major_idx_mm}) {len_f}) meta m0 \
                 {meta_eq_m0} \
                 hstrict)",
                major_idx_mm = major_idx_of("mm"),
            );
            let strict_arm = format!(
                "(fun (hstrict : Le (Nat.succ {major_idx}) {len_f}) => \
                 iota_reduct_app_inner env f a e1 {hwin} hsome C \
                 (fun (f1 : KExpr) (hf1 : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) => \
                 option_none_ne_some KExpr f1 C \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct env f) (OptionType.some KExpr f1) \
                 (Eq.symm (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) hnone) hf1)))"
            );

            let value = format!(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr) \
                 (hsome : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
                 (hnone : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
                 (C : Prop) (k : {k_type}) => \
                 iota_reduct_some_inv env (KExpr.app f a) e1 C hsome \
                 (fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : {h3_type}) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_app}) (OptionType.some KExpr e1)) => \
                 nat_le_succ_or {major_idx} {len_f} {hle} C \
                 {keq_arm} \
                 {strict_arm})",
                k_type = k_type,
                h3_type = h3_type,
                reduct_app = reduct_app,
                major_idx = major_idx,
                len_f = len_f,
                hle = hle,
                keq_arm = keq_arm,
                strict_arm = strict_arm,
            );

            let type_src = format!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (e1 : KExpr), \
                 Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> \
                 Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> \
                 forall (C : Prop), {k_type} -> C",
                k_type = k_type,
            );

            self.add_definition(SpecDefinition {
                name: "iota_reduct_app_minimal_boundary_idx".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "Boundary lemma + index: like iota_reduct_app_minimal_boundary but the continuation additionally receives Eq Nat major_idx (length (kapp_args f)) (the EQUAL-arm index identity). The par-reduction redex reconstruction (iota_reduct_par_app_redex) consumes BOTH major = a and major_idx = length(kapp_args f) to locate the major at the boundary of the reduced spine kapp_args f' (same length). DerivedProved, zero axiom_deps. Part of #2859 ((iota,app) minimal join).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "iota_reduct_app_inner".to_string(),
                    "list_head_drop_some_le_succ".to_string(),
                    "list_head_drop_len_append".to_string(),
                    "list_length_append_singleton".to_string(),
                    "le_pred_pred".to_string(),
                    "nat_le_succ_or".to_string(),
                    "kapp_args_app".to_string(),
                    "kapp_fn_app".to_string(),
                    "option_some_inj".to_string(),
                    "option_none_ne_some".to_string(),
                    "Le".to_string(),
                    "Eq.subst".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // =====================================================================
        // LIFT E-core (#2859 (beta,beta) cross-cases): the lift_at analogue of the
        // instantiate_at E-core. lift_at NEVER changes a const/recursor/constructor
        // head — it only shifts bvar indices, and a bvar head stays a bvar head — so
        // every segment-survival is UNCONDITIONAL (no head-const guard, unlike the
        // inst versions whose guard handles inst possibly replacing a bvar head).
        // Mirrors apply_spine3_inst / kapp_drop_inst / kapp_take_inst /
        // kapp_fields_inst / iota_reduct_inst_eq / iota_subst_commutes, with
        // (fun a0 => lift_at a0 c a) in place of (fun a0 => instantiate_at a0 v d)
        // and the guards/hypotheses dropped.
        // =====================================================================

        // 1. lift_at_apply_spine: lift_at distributes through the application spine —
        // UNCONDITIONAL (no const-head guard; pure structural distribution over app).
        // Mirror of instantiate_at_apply_spine: ListType.rec on args, chained through
        // apply_spine_cons + lift_at_app + list_map_cons + the head IH.
        // F := (fun a0 => lift_at a0 c a).
        {
            let f = "(fun (a0 : KExpr) => lift_at a0 c a)";
            self.add_definition(SpecDefinition {
                name: "lift_at_apply_spine".to_string(),
                type_src: format!(
                    concat!(
                        "forall (args : ListType KExpr) (head : KExpr) (c : Nat) (a : Nat), ",
                        "Eq KExpr (lift_at (apply_spine args head) c a) ",
                        "(apply_spine (list_map {f} args) (lift_at head c a))"
                    ),
                    f = f,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (args : ListType KExpr) (head : KExpr) (c : Nat) (a : Nat) => ",
                        "ListType.rec KExpr ",
                        "(fun (args0 : ListType KExpr) => forall (head0 : KExpr), ",
                        "Eq KExpr (lift_at (apply_spine args0 head0) c a) ",
                        "(apply_spine (list_map {f} args0) (lift_at head0 c a))) ",
                        // nil case
                        "(fun (head0 : KExpr) => ",
                        "Eq.trans KExpr ",
                        "(lift_at (apply_spine (ListType.nil KExpr) head0) c a) ",
                        "(lift_at head0 c a) ",
                        "(apply_spine (list_map {f} (ListType.nil KExpr)) (lift_at head0 c a)) ",
                        "(Eq.cong KExpr KExpr (fun (X : KExpr) => lift_at X c a) ",
                        "(apply_spine (ListType.nil KExpr) head0) head0 (apply_spine_nil head0)) ",
                        "(Eq.symm KExpr ",
                        "(apply_spine (list_map {f} (ListType.nil KExpr)) (lift_at head0 c a)) ",
                        "(lift_at head0 c a) ",
                        "(Eq.trans KExpr ",
                        "(apply_spine (list_map {f} (ListType.nil KExpr)) (lift_at head0 c a)) ",
                        "(apply_spine (ListType.nil KExpr) (lift_at head0 c a)) ",
                        "(lift_at head0 c a) ",
                        "(Eq.cong (ListType KExpr) KExpr ",
                        "(fun (L : ListType KExpr) => apply_spine L (lift_at head0 c a)) ",
                        "(list_map {f} (ListType.nil KExpr)) (ListType.nil KExpr) (list_map_nil {f})) ",
                        "(apply_spine_nil (lift_at head0 c a))))) ",
                        // cons case
                        "(fun (x : KExpr) (rest : ListType KExpr) ",
                        "(ih : forall (head0 : KExpr), ",
                        "Eq KExpr (lift_at (apply_spine rest head0) c a) ",
                        "(apply_spine (list_map {f} rest) (lift_at head0 c a))) => ",
                        "fun (head0 : KExpr) => ",
                        "Eq.trans KExpr ",
                        "(lift_at (apply_spine (ListType.cons KExpr x rest) head0) c a) ",
                        "(apply_spine (list_map {f} rest) (KExpr.app (lift_at head0 c a) (lift_at x c a))) ",
                        "(apply_spine (list_map {f} (ListType.cons KExpr x rest)) (lift_at head0 c a)) ",
                        // leg1
                        "(Eq.trans KExpr ",
                        "(lift_at (apply_spine (ListType.cons KExpr x rest) head0) c a) ",
                        "(apply_spine (list_map {f} rest) (lift_at (KExpr.app head0 x) c a)) ",
                        "(apply_spine (list_map {f} rest) (KExpr.app (lift_at head0 c a) (lift_at x c a))) ",
                        "(Eq.trans KExpr ",
                        "(lift_at (apply_spine (ListType.cons KExpr x rest) head0) c a) ",
                        "(lift_at (apply_spine rest (KExpr.app head0 x)) c a) ",
                        "(apply_spine (list_map {f} rest) (lift_at (KExpr.app head0 x) c a)) ",
                        "(Eq.cong KExpr KExpr (fun (X : KExpr) => lift_at X c a) ",
                        "(apply_spine (ListType.cons KExpr x rest) head0) (apply_spine rest (KExpr.app head0 x)) ",
                        "(apply_spine_cons x rest head0)) ",
                        "(ih (KExpr.app head0 x))) ",
                        "(Eq.cong KExpr KExpr (fun (Y : KExpr) => apply_spine (list_map {f} rest) Y) ",
                        "(lift_at (KExpr.app head0 x) c a) ",
                        "(KExpr.app (lift_at head0 c a) (lift_at x c a)) ",
                        "(lift_at_app head0 x c a))) ",
                        // leg2 (symm of RHS forward chain)
                        "(Eq.symm KExpr ",
                        "(apply_spine (list_map {f} (ListType.cons KExpr x rest)) (lift_at head0 c a)) ",
                        "(apply_spine (list_map {f} rest) (KExpr.app (lift_at head0 c a) (lift_at x c a))) ",
                        "(Eq.trans KExpr ",
                        "(apply_spine (list_map {f} (ListType.cons KExpr x rest)) (lift_at head0 c a)) ",
                        "(apply_spine (ListType.cons KExpr (lift_at x c a) (list_map {f} rest)) (lift_at head0 c a)) ",
                        "(apply_spine (list_map {f} rest) (KExpr.app (lift_at head0 c a) (lift_at x c a))) ",
                        "(Eq.cong (ListType KExpr) KExpr ",
                        "(fun (L : ListType KExpr) => apply_spine L (lift_at head0 c a)) ",
                        "(list_map {f} (ListType.cons KExpr x rest)) ",
                        "(ListType.cons KExpr (lift_at x c a) (list_map {f} rest)) ",
                        "(list_map_cons {f} x rest)) ",
                        "(apply_spine_cons (lift_at x c a) (list_map {f} rest) (lift_at head0 c a))))) ",
                        "args head"
                    ),
                    f = f,
                )),
                is_axiom: false,
                description: concat!(
                    "lift_at (apply_spine args head) c a = apply_spine (list_map (lift_at . c a) args) ",
                    "(lift_at head c a): lift_at distributes through the application spine. UNCONDITIONAL ",
                    "(no const-head guard; lift_at never changes the head). By ListType.rec on args through ",
                    "apply_spine_cons + lift_at_app + list_map_cons + the head IH. The lift analogue of ",
                    "instantiate_at_apply_spine. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "apply_spine".to_string(),
                    "list_map".to_string(),
                    "ListType.rec".to_string(),
                    "apply_spine_nil".to_string(),
                    "apply_spine_cons".to_string(),
                    "list_map_nil".to_string(),
                    "list_map_cons".to_string(),
                    "lift_at_app".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // kapp_args_lift_bvar: kapp_args (lift_bvar_at i c a) = nil. lift_bvar_at is
        // a Nat.rec over (Nat.sub c i) whose BOTH branches are a KExpr.bvar (different
        // bvar, but still a bvar), and kapp_args of any bvar is nil. Nat.rec on
        // (Nat.sub c i): zero branch gives kapp_args (bvar (add i a)) = nil (refl),
        // succ branch gives kapp_args (bvar i) = nil (refl). The lift bvar arm needs
        // this since lift never turns a bvar head into an app (unlike inst, which the
        // const-head guard discharges away).
        self.add_definition(SpecDefinition {
            name: "kapp_args_lift_bvar".to_string(),
            type_src: "forall (i : Nat) (c : Nat) (a : Nat), Eq (ListType KExpr) (kapp_args (lift_bvar_at i c a)) (ListType.nil KExpr)".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (c : Nat) (a : Nat) => ",
                "Nat.rec ",
                "(fun (k : Nat) => Eq (ListType KExpr) ",
                "(kapp_args (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i a)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) ",
                "(ListType.nil KExpr)) ",
                // zero branch: Nat.rec ... Nat.zero = KExpr.bvar (Nat.add i a); kapp_args = nil
                "(Eq.refl (ListType KExpr) (ListType.nil KExpr)) ",
                // succ branch: Nat.rec ... (succ k) = KExpr.bvar i; kapp_args = nil
                "(fun (k : Nat) (_ih : Eq (ListType KExpr) ",
                "(kapp_args (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i a)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k)) ",
                "(ListType.nil KExpr)) => ",
                "Eq.refl (ListType KExpr) (ListType.nil KExpr)) ",
                "(Nat.sub c i)",
            ).to_string()),
            is_axiom: false,
            description: "kapp_args (lift_bvar_at i c a) = nil: lift_bvar_at is a Nat.rec over (Nat.sub c i) whose both branches are a KExpr.bvar, and kapp_args of any bvar is nil. Nat.rec on (Nat.sub c i), each branch refl. The lift bvar arm helper (lift never turns a bvar head into an app). DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "lift_bvar_at".to_string(),
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // 2. lift_at_kapp_args: kapp_args commutes with lift_at up to list_map —
        // UNCONDITIONAL (no head-const guard; lift never changes the head structure).
        // Mirror of instantiate_at_kapp_args_const but UNCONDITIONAL: KExpr.rec on e.
        //   const arm: kapp_args (const) = nil, lift_at (const) = const, both nil (refl).
        //   sort/lam/pi arms: kapp_args = nil and lift_at preserves the ctor (sort->sort,
        //     lam->lam, pi->pi), both sides nil (refl); list_map_nil on the rhs.
        //   bvar arm: lift_at (bvar i) = lift_bvar_at i c a (still a bvar), kapp_args = nil
        //     via kapp_args_lift_bvar; list_map_nil on the rhs.
        //   app arm: genuine chain (kapp_args_app + lift_at_app + IH + list_map_append).
        // F := (fun a0 => lift_at a0 c a).
        {
            let fmap = "(fun (a0 : KExpr) => lift_at a0 c a)";
            // goal(E) : kapp_args commutes with lift_at (up to list_map).
            let goal = |e: &str| -> String {
                format!(
                    "Eq (ListType KExpr) (kapp_args (lift_at {e} c a)) (list_map {fmap} (kapp_args {e}))"
                )
            };
            // nil-head arm discharged GENUINELY: both sides reduce to nil. `nilrhs`
            // rewrites list_map F nil -> nil; `lhs_to_nil` proves kapp_args (lift_at
            // ctor) = nil.  For sort/lam/pi the lhs is refl-nil; for bvar it uses
            // kapp_args_lift_bvar.
            let nil_arm = |ctor: &str, lhs_to_nil: &str| -> String {
                format!(
                    concat!(
                        "Eq.trans (ListType KExpr) ",
                        "(kapp_args (lift_at {ctor} c a)) (ListType.nil KExpr) (list_map {fmap} (kapp_args {ctor})) ",
                        "{lhs_to_nil} ",
                        "(Eq.symm (ListType KExpr) (list_map {fmap} (kapp_args {ctor})) (ListType.nil KExpr) ",
                        "(Eq.trans (ListType KExpr) (list_map {fmap} (kapp_args {ctor})) (list_map {fmap} (ListType.nil KExpr)) (ListType.nil KExpr) ",
                        "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map {fmap} L) ",
                        "(kapp_args {ctor}) (ListType.nil KExpr) (Eq.refl (ListType KExpr) (ListType.nil KExpr))) ",
                        "(list_map_nil {fmap})))"
                    ),
                    ctor = ctor,
                    fmap = fmap,
                    lhs_to_nil = lhs_to_nil,
                )
            };
            // sort/lam/pi: kapp_args (lift_at ctor) = nil by refl (lift_at sort=sort,
            // lam=lam, pi=pi all defeq through lift_at_sort/lam/pi; kapp_args nil refl).
            let refl_nil = |ctor: &str| -> String {
                format!(
                    "(Eq.refl (ListType KExpr) (kapp_args (lift_at {ctor} c a)))",
                    ctor = ctor
                )
            };
            let disch_sort = nil_arm("(KExpr.sort n)", &refl_nil("(KExpr.sort n)"));
            // bvar: lift_at (bvar i) c a = lift_bvar_at i c a; kapp_args = nil via helper.
            let disch_bvar = nil_arm("(KExpr.bvar i)", "(kapp_args_lift_bvar i c a)");
            let disch_lam = nil_arm("(KExpr.lam ty b)", &refl_nil("(KExpr.lam ty b)"));
            let disch_pi = nil_arm("(KExpr.pi ty b)", &refl_nil("(KExpr.pi ty b)"));
            // let_ arm: nil like sort/lam/pi. lift_at (let_ ..) preserves the let ctor
            // (lift_at_let_) and kapp_args (let_ ..) = nil, so both sides refl-nil.
            let disch_let = nil_arm("(KExpr.let_ ty v b)", &refl_nil("(KExpr.let_ ty v b)"));
            let disch_proj = nil_arm("(KExpr.proj s i sub)", &refl_nil("(KExpr.proj s i sub)"));
            let disch_lit = nil_arm("(KExpr.lit m)", &refl_nil("(KExpr.lit m)"));
            // The meeting point M for the app arm.
            let meet = format!(
                "(list_append (list_map {fmap} (kapp_args f)) (ListType.cons KExpr (lift_at a0 c a) (ListType.nil KExpr)))"
            );
            let app_arm = format!(
                concat!(
                    "(fun (f : KExpr) (a0 : KExpr) ",
                    "(ihf : {goal_f}) (_iha : {goal_a}) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(kapp_args (lift_at (KExpr.app f a0) c a)) {meet} (list_map {fmap} (kapp_args (KExpr.app f a0))) ",
                    // LHS -> M
                    "(Eq.trans (ListType KExpr) ",
                    "(kapp_args (lift_at (KExpr.app f a0) c a)) ",
                    "(kapp_args (KExpr.app (lift_at f c a) (lift_at a0 c a))) {meet} ",
                    "(Eq.cong KExpr (ListType KExpr) (fun (X : KExpr) => kapp_args X) ",
                    "(lift_at (KExpr.app f a0) c a) (KExpr.app (lift_at f c a) (lift_at a0 c a)) ",
                    "(lift_at_app f a0 c a)) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(kapp_args (KExpr.app (lift_at f c a) (lift_at a0 c a))) ",
                    "(list_append (kapp_args (lift_at f c a)) (ListType.cons KExpr (lift_at a0 c a) (ListType.nil KExpr))) ",
                    "{meet} ",
                    "(kapp_args_app (lift_at f c a) (lift_at a0 c a)) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                    "(fun (L : ListType KExpr) => list_append L (ListType.cons KExpr (lift_at a0 c a) (ListType.nil KExpr))) ",
                    "(kapp_args (lift_at f c a)) (list_map {fmap} (kapp_args f)) ihf))) ",
                    // M -> RHS  (symm of RHS -> M)
                    "(Eq.symm (ListType KExpr) (list_map {fmap} (kapp_args (KExpr.app f a0))) {meet} ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map {fmap} (kapp_args (KExpr.app f a0))) ",
                    "(list_map {fmap} (list_append (kapp_args f) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "{meet} ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map {fmap} L) ",
                    "(kapp_args (KExpr.app f a0)) (list_append (kapp_args f) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                    "(kapp_args_app f a0)) ",
                    "(Eq.trans (ListType KExpr) ",
                    "(list_map {fmap} (list_append (kapp_args f) (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_append (list_map {fmap} (kapp_args f)) (list_map {fmap} (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "{meet} ",
                    "(list_map_append {fmap} (kapp_args f) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                    "(fun (L : ListType KExpr) => list_append (list_map {fmap} (kapp_args f)) L) ",
                    "(list_map {fmap} (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                    "(ListType.cons KExpr (lift_at a0 c a) (ListType.nil KExpr)) ",
                    "(list_map_cons {fmap} a0 (ListType.nil KExpr)))))))"
                ),
                goal_f = goal("f"),
                goal_a = goal("a0"),
                fmap = fmap,
                meet = meet,
            );
            let kapp_args_value = format!(
                concat!(
                    "fun (c : Nat) (a : Nat) (e : KExpr) => ",
                    "KExpr.rec ",
                    "(fun (e0 : KExpr) => {goal_e0}) ",
                    "(fun (n : Level) => {disch_sort}) ",
                    "(fun (i : Nat) => {disch_bvar}) ",
                    "{app_arm} ",
                    "(fun (ty : KExpr) (b : KExpr) (_ihty : {goal_ty}) (_ihb : {goal_b}) => {disch_lam}) ",
                    "(fun (ty : KExpr) (b : KExpr) (_ihty : {goal_ty}) (_ihb : {goal_b}) => {disch_pi}) ",
                    "(fun (nm0 : Name) (us : ListType Level) => ",
                    "Eq.refl (ListType KExpr) (ListType.nil KExpr)) ",
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_ihty : {goal_ty}) (_ihv : {goal_v}) (_ihb : {goal_b}) => {disch_let}) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : {goal_sub}) => {disch_proj}) ",
                    "(fun (m : Nat) => {disch_lit}) ",
                    "e"
                ),
                goal_e0 = goal("e0"),
                disch_sort = disch_sort,
                disch_bvar = disch_bvar,
                app_arm = app_arm,
                goal_ty = goal("ty"),
                goal_b = goal("b"),
                disch_lam = disch_lam,
                disch_pi = disch_pi,
                goal_v = goal("v"),
                disch_let = disch_let,
                goal_sub = goal("sub"),
                disch_proj = disch_proj,
                disch_lit = disch_lit,
            );
            self.add_definition(SpecDefinition {
                name: "lift_at_kapp_args".to_string(),
                type_src: format!(
                    "forall (c : Nat) (a : Nat) (e : KExpr), {goal}",
                    goal = goal("e"),
                ),
                value_src: Some(kapp_args_value),
                is_axiom: false,
                description: concat!(
                    "kapp_args commutes with lift_at up to list_map: kapp_args (lift_at e c a) = ",
                    "list_map (lift_at . c a) (kapp_args e). UNCONDITIONAL (no const-head guard; lift never ",
                    "changes the head structure). KExpr.rec on e — const arm reduces to nil (refl), ",
                    "sort/lam/pi arms nil (lift preserves the ctor), bvar arm nil via kapp_args_lift_bvar, ",
                    "app arm a chain (kapp_args_app + lift_at_app + IH + list_map_append). The lift analogue ",
                    "of instantiate_at_kapp_args_const. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kapp_args".to_string(),
                    "lift_at".to_string(),
                    "lift_at_app".to_string(),
                    "kapp_args_app".to_string(),
                    "kapp_args_lift_bvar".to_string(),
                    "list_map".to_string(),
                    "list_map_append".to_string(),
                    "list_map_cons".to_string(),
                    "list_map_nil".to_string(),
                    "KExpr.rec".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // kexpr_const_name_kapp_fn_lift_bvar: kexpr_const_name (kapp_fn (lift_bvar_at
        // i c a)) = none. lift_bvar_at is a Nat.rec over (Nat.sub c i) whose both
        // branches are a KExpr.bvar; kapp_fn of a bvar is that bvar; kexpr_const_name
        // of a bvar is none. Nat.rec on (Nat.sub c i), each branch refl. The bvar arm
        // helper for kexpr_const_name_lift (lift never gives a bvar head a const name).
        self.add_definition(SpecDefinition {
            name: "kexpr_const_name_kapp_fn_lift_bvar".to_string(),
            type_src: "forall (i : Nat) (c : Nat) (a : Nat), Eq (OptionType Name) (kexpr_const_name (kapp_fn (lift_bvar_at i c a))) (OptionType.none Name)".to_string(),
            value_src: Some(concat!(
                "fun (i : Nat) (c : Nat) (a : Nat) => ",
                "Nat.rec ",
                "(fun (k : Nat) => Eq (OptionType Name) ",
                "(kexpr_const_name (kapp_fn (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i a)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k))) ",
                "(OptionType.none Name)) ",
                "(Eq.refl (OptionType Name) (OptionType.none Name)) ",
                "(fun (k : Nat) (_ih : Eq (OptionType Name) ",
                "(kexpr_const_name (kapp_fn (Nat.rec (fun (_ : Nat) => KExpr) (KExpr.bvar (Nat.add i a)) (fun (_ : Nat) (_ : KExpr) => KExpr.bvar i) k))) ",
                "(OptionType.none Name)) => ",
                "Eq.refl (OptionType Name) (OptionType.none Name)) ",
                "(Nat.sub c i)",
            ).to_string()),
            is_axiom: false,
            description: "kexpr_const_name (kapp_fn (lift_bvar_at i c a)) = none: lift_bvar_at is a Nat.rec over (Nat.sub c i) whose both branches are a KExpr.bvar; kapp_fn of a bvar is that bvar; kexpr_const_name of a bvar is none. Nat.rec on (Nat.sub c i), each branch refl. The bvar arm helper for kexpr_const_name_lift. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "lift_bvar_at".to_string(),
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // 3. kexpr_const_name_lift: the head const-name survives lift_at —
        // UNCONDITIONAL. kexpr_const_name (kapp_fn (lift_at e c a)) = kexpr_const_name
        // (kapp_fn e). The lift analogue of kexpr_const_name_instantiate_const, but no
        // guard (lift never changes the head). KExpr.rec on e:
        //   const arm: both sides some nm0 (refl).
        //   app arm: kapp_fn (lift (app f a0)) = kapp_fn (lift f), IH on f.
        //   sort/lam/pi arms: both sides none (lift preserves the ctor; refl).
        //   bvar arm: lift (bvar i) = lift_bvar_at i c a; LHS none via
        //     kexpr_const_name_kapp_fn_lift_bvar, RHS none (refl).
        {
            let goal = |e: &str| -> String {
                format!(
                    "Eq (OptionType Name) (kexpr_const_name (kapp_fn (lift_at {e} c a))) (kexpr_const_name (kapp_fn {e}))"
                )
            };
            // sort/lam/pi: both sides reduce to none by refl.
            let refl_none = |ctor: &str| -> String {
                format!(
                    "(Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn (lift_at {ctor} c a))))",
                    ctor = ctor
                )
            };
            // bvar: LHS = none via helper; RHS kexpr_const_name (kapp_fn (bvar i)) = none (refl).
            let bvar_arm = concat!(
                "Eq.trans (OptionType Name) ",
                "(kexpr_const_name (kapp_fn (lift_at (KExpr.bvar i) c a))) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.bvar i))) ",
                "(kexpr_const_name_kapp_fn_lift_bvar i c a) ",
                "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.bvar i))) (OptionType.none Name) ",
                "(Eq.refl (OptionType Name) (OptionType.none Name)))"
            );
            // app: kapp_fn (lift_at (app f a0)) = kapp_fn (lift_at f); RHS = kexpr_const_name (kapp_fn f); IH on f.
            let app_arm = format!(
                concat!(
                    "(fun (f : KExpr) (a0 : KExpr) (ihf : {goal_f}) (_iha : {goal_a}) => ",
                    "Eq.trans (OptionType Name) ",
                    "(kexpr_const_name (kapp_fn (lift_at (KExpr.app f a0) c a))) ",
                    "(kexpr_const_name (kapp_fn (lift_at f c a))) ",
                    "(kexpr_const_name (kapp_fn (KExpr.app f a0))) ",
                    // LHS = kexpr_const_name (kapp_fn (lift f)) :
                    //   kapp_fn (lift (app f a0)) = kapp_fn (app (lift f)(lift a0)) = kapp_fn (lift f)
                    "(Eq.cong KExpr (OptionType Name) (fun (X : KExpr) => kexpr_const_name (kapp_fn X)) ",
                    "(lift_at (KExpr.app f a0) c a) (KExpr.app (lift_at f c a) (lift_at a0 c a)) ",
                    "(lift_at_app f a0 c a)) ",
                    // kexpr_const_name (kapp_fn (lift f)) = kexpr_const_name (kapp_fn f) [ihf];
                    // kexpr_const_name (kapp_fn (app f a0)) = kexpr_const_name (kapp_fn f) [defeq, refl]
                    "(Eq.trans (OptionType Name) ",
                    "(kexpr_const_name (kapp_fn (lift_at f c a))) ",
                    "(kexpr_const_name (kapp_fn f)) ",
                    "(kexpr_const_name (kapp_fn (KExpr.app f a0))) ",
                    "ihf ",
                    "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a0))) (kexpr_const_name (kapp_fn f)) ",
                    "(Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn f))))))"
                ),
                goal_f = goal("f"),
                goal_a = goal("a0"),
            );
            let value = format!(
                concat!(
                    "fun (c : Nat) (a : Nat) (e : KExpr) => ",
                    "KExpr.rec ",
                    "(fun (e0 : KExpr) => {goal_e0}) ",
                    "(fun (n : Level) => {disch_sort}) ",
                    "(fun (i : Nat) => {bvar_arm}) ",
                    "{app_arm} ",
                    "(fun (ty : KExpr) (b : KExpr) (_ihty : {goal_ty}) (_ihb : {goal_b}) => {disch_lam}) ",
                    "(fun (ty : KExpr) (b : KExpr) (_ihty : {goal_ty}) (_ihb : {goal_b}) => {disch_pi}) ",
                    "(fun (nm0 : Name) (us : ListType Level) => ",
                    "Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn (lift_at (KExpr.const nm0 us) c a)))) ",
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) (_ihty : {goal_ty}) (_ihv : {goal_v}) (_ihb : {goal_b}) => {disch_let}) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : {goal_sub}) => {disch_proj}) ",
                    "(fun (m : Nat) => {disch_lit}) ",
                    "e"
                ),
                goal_e0 = goal("e0"),
                disch_sort = refl_none("(KExpr.sort n)"),
                bvar_arm = bvar_arm,
                app_arm = app_arm,
                goal_ty = goal("ty"),
                goal_b = goal("b"),
                disch_lam = refl_none("(KExpr.lam ty b)"),
                disch_pi = refl_none("(KExpr.pi ty b)"),
                goal_v = goal("v"),
                disch_let = refl_none("(KExpr.let_ ty v b)"),
                goal_sub = goal("sub"),
                disch_proj = refl_none("(KExpr.proj s i sub)"),
                disch_lit = refl_none("(KExpr.lit m)"),
            );
            self.add_definition(SpecDefinition {
                name: "kexpr_const_name_lift".to_string(),
                type_src: format!(
                    "forall (c : Nat) (a : Nat) (e : KExpr), {goal}",
                    goal = goal("e"),
                ),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "Under no hypothesis (UNCONDITIONAL), the head const-name survives lift_at: ",
                    "kexpr_const_name (kapp_fn (lift_at e c a)) = kexpr_const_name (kapp_fn e). So ",
                    "iota_reduct(lift e) looks up the same recursor/constructor. KExpr.rec on e — const arm ",
                    "genuine (some nm0), app arm recursive (kapp_fn peels through the lifted app), ",
                    "sort/lam/pi arms none (lift preserves the ctor), bvar arm none via ",
                    "kexpr_const_name_kapp_fn_lift_bvar. The lift analogue of ",
                    "kexpr_const_name_instantiate_const, no guard. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kexpr_const_name".to_string(),
                    "kapp_fn".to_string(),
                    "lift_at".to_string(),
                    "lift_at_app".to_string(),
                    "kexpr_const_name_kapp_fn_lift_bvar".to_string(),
                    "KExpr.rec".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // 4. The segment-survival lemmas under lift (UNCONDITIONAL). Mirror
        // kapp_drop_inst / kapp_take_inst / kapp_fields_inst, but use lift_at_kapp_args
        // (no guard) in place of instantiate_at_kapp_args_const (guarded).
        // F := (fun a0 => lift_at a0 c a).
        let flift = "(fun (a0 : KExpr) => lift_at a0 c a)";

        // kapp_drop_lift: list_drop kk (kapp_args (lift e)) = list_map F (list_drop kk (kapp_args e)).
        self.add_definition(SpecDefinition {
            name: "kapp_drop_lift".to_string(),
            type_src: concat!(
                "forall (c : Nat) (a : Nat) (e : KExpr) (kk : Nat), ",
                "Eq (ListType KExpr) (list_drop kk (kapp_args (lift_at e c a))) ",
                "(list_map (fun (a0 : KExpr) => lift_at a0 c a) (list_drop kk (kapp_args e)))"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (c : Nat) (a : Nat) (e : KExpr) (kk : Nat) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_drop kk (kapp_args (lift_at e c a))) ",
                    "(list_drop kk (list_map {f} (kapp_args e))) ",
                    "(list_map {f} (list_drop kk (kapp_args e))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop kk L) ",
                    "(kapp_args (lift_at e c a)) (list_map {f} (kapp_args e)) ",
                    "(lift_at_kapp_args c a e)) ",
                    "(list_map_drop {f} kk (kapp_args e))"
                ),
                f = flift,
            )),
            is_axiom: false,
            description: "list_drop kk (kapp_args (lift e)) = list_map (lift .) (list_drop kk (kapp_args e)) — UNCONDITIONAL (lift analogue of kapp_drop_inst). Part of #2859 (LIFT E-core).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "list_drop".to_string(),
                "list_map".to_string(),
                "lift_at_kapp_args".to_string(),
                "list_map_drop".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_take_lift: list_take pn (kapp_args (lift e)) = list_map F (list_take pn (kapp_args e)).
        self.add_definition(SpecDefinition {
            name: "kapp_take_lift".to_string(),
            type_src: concat!(
                "forall (c : Nat) (a : Nat) (e : KExpr) (pn : Nat), ",
                "Eq (ListType KExpr) (list_take pn (kapp_args (lift_at e c a))) ",
                "(list_map (fun (a0 : KExpr) => lift_at a0 c a) (list_take pn (kapp_args e)))"
            )
            .to_string(),
            value_src: Some(format!(
                concat!(
                    "fun (c : Nat) (a : Nat) (e : KExpr) (pn : Nat) => ",
                    "Eq.trans (ListType KExpr) ",
                    "(list_take pn (kapp_args (lift_at e c a))) ",
                    "(list_take pn (list_map {f} (kapp_args e))) ",
                    "(list_map {f} (list_take pn (kapp_args e))) ",
                    "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_take pn L) ",
                    "(kapp_args (lift_at e c a)) (list_map {f} (kapp_args e)) ",
                    "(lift_at_kapp_args c a e)) ",
                    "(list_map_take {f} pn (kapp_args e))"
                ),
                f = flift,
            )),
            is_axiom: false,
            description: "list_take pn (kapp_args (lift e)) = list_map (lift .) (list_take pn (kapp_args e)) — UNCONDITIONAL (lift analogue of kapp_take_inst). Part of #2859 (LIFT E-core).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "list_take".to_string(),
                "list_map".to_string(),
                "lift_at_kapp_args".to_string(),
                "list_map_take".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_fields_lift: the fields segment survives lift (UNCONDITIONAL). Mirror
        // of kapp_fields_inst: the offset (list_length (kapp_args major) - nf) is
        // preserved by list_map_length; the offset rewrite uses list_drop_cong.
        {
            let fields_off = "(Nat.sub (list_length (kapp_args major)) nf)";
            let fields_off_lift = "(Nat.sub (list_length (kapp_args (lift_at major c a))) nf)";
            let fields_off_mid = "(Nat.sub (list_length (list_map (fun (a0 : KExpr) => lift_at a0 c a) (kapp_args major))) nf)";
            self.add_definition(SpecDefinition {
                name: "kapp_fields_lift".to_string(),
                type_src: format!(
                    concat!(
                        "forall (c : Nat) (a : Nat) (major : KExpr) (nf : Nat), ",
                        "Eq (ListType KExpr) (list_drop {off_i} (kapp_args (lift_at major c a))) ",
                        "(list_map (fun (a0 : KExpr) => lift_at a0 c a) (list_drop {off} (kapp_args major)))"
                    ),
                    off_i = fields_off_lift,
                    off = fields_off,
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (c : Nat) (a : Nat) (major : KExpr) (nf : Nat) => ",
                        "Eq.trans (ListType KExpr) ",
                        "(list_drop {off_i} (kapp_args (lift_at major c a))) ",
                        "(list_drop {off} (list_map {f} (kapp_args major))) ",
                        "(list_map {f} (list_drop {off} (kapp_args major))) ",
                        // s1 = s_off ∘ s_list
                        "(Eq.trans (ListType KExpr) ",
                        "(list_drop {off_i} (kapp_args (lift_at major c a))) ",
                        "(list_drop {off} (kapp_args (lift_at major c a))) ",
                        "(list_drop {off} (list_map {f} (kapp_args major))) ",
                        // s_off: rewrite offset off_i -> off (list fixed), via list_drop_cong.
                        "(list_drop_cong {off_i} {off} (kapp_args (lift_at major c a)) ",
                        // eoff : off_i = off  =  eoff1 ∘ eoff2
                        "(Eq.trans Nat {off_i} {off_mid} {off} ",
                        // eoff1: KA_AM -> MAP_KA_M inside list_length.
                        "(Eq.cong (ListType KExpr) Nat ",
                        "(fun (L : ListType KExpr) => Nat.sub (list_length L) nf) ",
                        "(kapp_args (lift_at major c a)) (list_map {f} (kapp_args major)) ",
                        "(lift_at_kapp_args c a major)) ",
                        // eoff2: collapse list_length (list_map F ..) -> list_length ..
                        "(Eq.cong Nat Nat (fun (q : Nat) => Nat.sub q nf) ",
                        "(list_length (list_map {f} (kapp_args major))) (list_length (kapp_args major)) ",
                        "(list_map_length {f} (kapp_args major))))) ",
                        // s_list: rewrite list KA_AM -> MAP_KA_M (offset fixed at off).
                        "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                        "(fun (L : ListType KExpr) => list_drop {off} L) ",
                        "(kapp_args (lift_at major c a)) (list_map {f} (kapp_args major)) ",
                        "(lift_at_kapp_args c a major))) ",
                        // s2: list_drop off (list_map F ..) = list_map F (list_drop off ..)
                        "(list_map_drop {f} {off} (kapp_args major))"
                    ),
                    f = flift,
                    off = fields_off,
                    off_i = fields_off_lift,
                    off_mid = fields_off_mid,
                )),
                is_axiom: false,
                description: "The fields segment survives lift (UNCONDITIONAL): list_drop (offset on lift major) (kapp_args (lift major)) = list_map (lift .) (list_drop (offset on major) (kapp_args major)). The offset is preserved by list_map_length; the offset rewrite uses list_drop_cong. Lift analogue of kapp_fields_inst. Part of #2859 (LIFT E-core).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kapp_args".to_string(),
                    "list_drop".to_string(),
                    "list_length".to_string(),
                    "list_map".to_string(),
                    "lift_at_kapp_args".to_string(),
                    "list_map_length".to_string(),
                    "list_map_drop".to_string(),
                    "list_drop_cong".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // lift_apply_spine3: lift_at distributes through the three nested apply_spine
        // layers of the iota reduct (extras / fields / prefix), pushing lift onto each
        // arg list (list_map) and onto the rhs head. Three nested lift_at_apply_spine.
        // The lift analogue of apply_spine3_inst. F := (fun a0 => lift_at a0 c a).
        {
            let fmap = "(fun (a0 : KExpr) => lift_at a0 c a)";
            let final_term = format!(
                "(apply_spine (list_map {fmap} la) (apply_spine (list_map {fmap} lb) (apply_spine (list_map {fmap} lc) (lift_at rhs c a))))"
            );
            self.add_definition(SpecDefinition {
                name: "lift_apply_spine3".to_string(),
                type_src: format!(
                    "forall (c : Nat) (a : Nat) (la : ListType KExpr) (lb : ListType KExpr) (lc : ListType KExpr) (rhs : KExpr), \
                     Eq KExpr (lift_at (apply_spine la (apply_spine lb (apply_spine lc rhs))) c a) {final_term}"
                ),
                value_src: Some(format!(
                    concat!(
                        "fun (c : Nat) (a : Nat) (la : ListType KExpr) (lb : ListType KExpr) (lc : ListType KExpr) (rhs : KExpr) => ",
                        "Eq.trans KExpr ",
                        "(lift_at (apply_spine la (apply_spine lb (apply_spine lc rhs))) c a) ",
                        "(apply_spine (list_map {fmap} la) (lift_at (apply_spine lb (apply_spine lc rhs)) c a)) ",
                        "{final_term} ",
                        "(lift_at_apply_spine la (apply_spine lb (apply_spine lc rhs)) c a) ",
                        "(Eq.trans KExpr ",
                        "(apply_spine (list_map {fmap} la) (lift_at (apply_spine lb (apply_spine lc rhs)) c a)) ",
                        "(apply_spine (list_map {fmap} la) (apply_spine (list_map {fmap} lb) (lift_at (apply_spine lc rhs) c a))) ",
                        "{final_term} ",
                        "(Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine (list_map {fmap} la) Z) ",
                        "(lift_at (apply_spine lb (apply_spine lc rhs)) c a) ",
                        "(apply_spine (list_map {fmap} lb) (lift_at (apply_spine lc rhs) c a)) ",
                        "(lift_at_apply_spine lb (apply_spine lc rhs) c a)) ",
                        "(Eq.cong KExpr KExpr ",
                        "(fun (Z : KExpr) => apply_spine (list_map {fmap} la) (apply_spine (list_map {fmap} lb) Z)) ",
                        "(lift_at (apply_spine lc rhs) c a) ",
                        "(apply_spine (list_map {fmap} lc) (lift_at rhs c a)) ",
                        "(lift_at_apply_spine lc rhs c a)))"
                    ),
                    fmap = fmap,
                    final_term = final_term,
                )),
                is_axiom: false,
                description: "lift_at distributes through the iota reduct's three nested apply_spine layers (pushing lift onto each arg list via list_map and onto the rhs head). Three nested lift_at_apply_spine. The lift analogue of apply_spine3_inst. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "apply_spine".to_string(),
                    "list_map".to_string(),
                    "lift_at".to_string(),
                    "lift_at_apply_spine".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // 6. iota_reduct_lift_eq: the REDUCT EQUATION under lift — the lift analogue of
        // iota_reduct_inst_eq. Given the redex witnesses (rule lookup h5; the original
        // reduct equation h5r : some REDUCT = some e') and a LIFT-CLOSED env, the
        // reduct recomputed on the lift side equals lift of the original reduct, which
        // equals lift e':  REDUCT_l = lift REDUCT = lift e'. NO head-const guards
        // needed (UNCONDITIONAL segment survival).
        {
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";
            let nf = "(recrule_num_fields rule)";
            let p_rhs = "(recrule_rhs rule)";
            let fmap = "(fun (a0 : KExpr) => lift_at a0 c a)";

            // original-side segments (on e / major)
            let ext = format!("(list_drop (Nat.succ {major_idx}) (kapp_args e))");
            let fld = format!(
                "(list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major))"
            );
            let pre = format!("(list_take {prefix_n} (kapp_args e))");
            let reduct =
                format!("(apply_spine {ext} (apply_spine {fld} (apply_spine {pre} {p_rhs})))");

            // lift-side segments (on lift e / lift major); rhs slot stays bare.
            let ext_l = format!("(list_drop (Nat.succ {major_idx}) (kapp_args (lift_at e c a)))");
            let fld_l = format!("(list_drop (Nat.sub (list_length (kapp_args (lift_at major c a))) {nf}) (kapp_args (lift_at major c a)))");
            let pre_l = format!("(list_take {prefix_n} (kapp_args (lift_at e c a)))");
            let reduct_l = format!(
                "(apply_spine {ext_l} (apply_spine {fld_l} (apply_spine {pre_l} {p_rhs})))"
            );

            // map-F versions + lift rhs + lift REDUCT.
            let mext = format!("(list_map {fmap} {ext})");
            let mfld = format!("(list_map {fmap} {fld})");
            let mpre = format!("(list_map {fmap} {pre})");
            let l_rhs = format!("(lift_at {p_rhs} c a)");
            let reduct_unfolded =
                format!("(apply_spine {mext} (apply_spine {mfld} (apply_spine {mpre} {l_rhs})))");
            let lift_reduct = format!("(lift_at {reduct} c a)");

            // inner: apply_spine pre_l rhs = apply_spine (map F pre) (lift rhs).
            let inner = format!(
                "(Eq.trans KExpr \
                 (apply_spine {pre_l} {p_rhs}) (apply_spine {mpre} {p_rhs}) (apply_spine {mpre} {l_rhs}) \
                 (Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L {p_rhs}) \
                 {pre_l} {mpre} (kapp_take_lift c a e {prefix_n})) \
                 (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine {mpre} Z) \
                 {p_rhs} {l_rhs} \
                 (Eq.symm KExpr {l_rhs} {p_rhs} (recenv_lift_closed_rhs env recname cname rule c a liftclosed h5))))"
            );

            // middle: apply_spine fld_l (apply_spine pre_l rhs)
            //       = apply_spine (map F fld) (apply_spine (map F pre) (lift rhs)).
            let middle = format!(
                "(Eq.trans KExpr \
                 (apply_spine {fld_l} (apply_spine {pre_l} {p_rhs})) \
                 (apply_spine {mfld} (apply_spine {pre_l} {p_rhs})) \
                 (apply_spine {mfld} (apply_spine {mpre} {l_rhs})) \
                 (Eq.cong (ListType KExpr) KExpr \
                 (fun (L : ListType KExpr) => apply_spine L (apply_spine {pre_l} {p_rhs})) \
                 {fld_l} {mfld} (kapp_fields_lift c a major {nf})) \
                 (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine {mfld} Z) \
                 (apply_spine {pre_l} {p_rhs}) (apply_spine {mpre} {l_rhs}) {inner}))"
            );

            // outer: REDUCT_l = apply_spine (map F ext) (apply_spine (map F fld) (apply_spine (map F pre) (lift rhs))).
            let outer = format!(
                "(Eq.trans KExpr \
                 {reduct_l} \
                 (apply_spine {mext} (apply_spine {fld_l} (apply_spine {pre_l} {p_rhs}))) \
                 {reduct_unfolded} \
                 (Eq.cong (ListType KExpr) KExpr \
                 (fun (L : ListType KExpr) => apply_spine L (apply_spine {fld_l} (apply_spine {pre_l} {p_rhs}))) \
                 {ext_l} {mext} (kapp_drop_lift c a e (Nat.succ {major_idx}))) \
                 (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine {mext} Z) \
                 (apply_spine {fld_l} (apply_spine {pre_l} {p_rhs})) \
                 (apply_spine {mfld} (apply_spine {mpre} {l_rhs})) {middle}))"
            );

            // spine_eq: REDUCT_l = lift REDUCT (outer ∘ symm lift_apply_spine3).
            let spine_eq = format!(
                "(Eq.trans KExpr {reduct_l} {reduct_unfolded} {lift_reduct} {outer} \
                 (Eq.symm KExpr {lift_reduct} {reduct_unfolded} \
                 (lift_apply_spine3 c a {ext} {fld} {pre} {p_rhs})))"
            );

            // lift_eq: lift REDUCT = lift e' (cong lift on option_some_inj h5r).
            let lift_eq = format!(
                "(Eq.cong KExpr KExpr {fmap} {reduct} e' (option_some_inj KExpr {reduct} e' h5r))"
            );

            let value = format!(
                "fun (env : RecEnv) (c : Nat) (a : Nat) (e : KExpr) (e' : KExpr) \
                 (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (liftclosed : RecEnvLiftClosed env) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e')) => \
                 Eq.trans KExpr {reduct_l} {lift_reduct} (lift_at e' c a) {spine_eq} {lift_eq}"
            );

            let type_src = format!(
                "forall (env : RecEnv) (c : Nat) (a : Nat) (e : KExpr) (e' : KExpr) \
                 (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
                 RecEnvLiftClosed env -> \
                 Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
                 Eq KExpr {reduct_l} (lift_at e' c a)"
            );

            self.add_definition(SpecDefinition {
                name: "iota_reduct_lift_eq".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: "The reduct equation of the LIFT E-core: under a lift-closed env, the iota reduct recomputed on the lift side equals lift of the original reduct (= lift e'). Composes kapp_drop/take/fields_lift (UNCONDITIONAL segment survival) + recenv_lift_closed_rhs (rhs slot) + lift_apply_spine3 (lift through apply_spine) + option_some_inj (REDUCT = e'). No head-const guards (unlike iota_reduct_inst_eq). The lift analogue. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kapp_args".to_string(),
                    "apply_spine".to_string(),
                    "list_map".to_string(),
                    "list_drop".to_string(),
                    "list_take".to_string(),
                    "recrule_rhs".to_string(),
                    "recrule_num_fields".to_string(),
                    "kapp_drop_lift".to_string(),
                    "kapp_take_lift".to_string(),
                    "kapp_fields_lift".to_string(),
                    "lift_apply_spine3".to_string(),
                    "recenv_lift_closed_rhs".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_major_lift: the major premise survives lift_at — UNCONDITIONAL. From
        // list_head (list_drop kk (kapp_args e)) = some major, conclude list_head
        // (list_drop kk (kapp_args (lift e))) = some (lift major). Chain:
        // lift_at_kapp_args (no guard) + list_map_drop + list_map_head + opt_map_some.
        // The level-3 reconstruction of the LIFT E-core; mirror of iota_major_inst.
        {
            let f = "(fun (a0 : KExpr) => lift_at a0 c a)";
            self.add_definition(SpecDefinition {
                name: "iota_major_lift".to_string(),
                type_src: concat!(
                    "forall (c : Nat) (a : Nat) (e : KExpr) (kk : Nat) (major : KExpr), ",
                    "Eq (OptionType KExpr) (list_head (list_drop kk (kapp_args e))) (OptionType.some KExpr major) -> ",
                    "Eq (OptionType KExpr) (list_head (list_drop kk (kapp_args (lift_at e c a)))) (OptionType.some KExpr (lift_at major c a))"
                )
                .to_string(),
                value_src: Some(format!(
                    concat!(
                        "fun (c : Nat) (a : Nat) (e : KExpr) (kk : Nat) (major : KExpr) ",
                        "(h3 : Eq (OptionType KExpr) (list_head (list_drop kk (kapp_args e))) (OptionType.some KExpr major)) => ",
                        "Eq.trans (OptionType KExpr) ",
                        "(list_head (list_drop kk (kapp_args (lift_at e c a)))) ",
                        "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                        "(OptionType.some KExpr (lift_at major c a)) ",
                        // LHS -> opt_map F (list_head (list_drop kk (kapp_args e)))
                        "(Eq.trans (OptionType KExpr) ",
                        "(list_head (list_drop kk (kapp_args (lift_at e c a)))) ",
                        "(list_head (list_drop kk (list_map {f} (kapp_args e)))) ",
                        "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                        "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop kk L)) ",
                        "(kapp_args (lift_at e c a)) (list_map {f} (kapp_args e)) ",
                        "(lift_at_kapp_args c a e)) ",
                        "(Eq.trans (OptionType KExpr) ",
                        "(list_head (list_drop kk (list_map {f} (kapp_args e)))) ",
                        "(list_head (list_map {f} (list_drop kk (kapp_args e)))) ",
                        "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                        "(Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) ",
                        "(list_drop kk (list_map {f} (kapp_args e))) (list_map {f} (list_drop kk (kapp_args e))) ",
                        "(list_map_drop {f} kk (kapp_args e))) ",
                        "(list_map_head {f} (list_drop kk (kapp_args e))))) ",
                        // opt_map F (...) -> some (lift major)
                        "(Eq.trans (OptionType KExpr) ",
                        "(opt_map {f} (list_head (list_drop kk (kapp_args e)))) ",
                        "(opt_map {f} (OptionType.some KExpr major)) ",
                        "(OptionType.some KExpr (lift_at major c a)) ",
                        "(Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (O : OptionType KExpr) => opt_map {f} O) ",
                        "(list_head (list_drop kk (kapp_args e))) (OptionType.some KExpr major) h3) ",
                        "(opt_map_some {f} major))"
                    ),
                    f = f,
                )),
                is_axiom: false,
                description: "The iota major premise survives lift_at (UNCONDITIONAL): list_head (list_drop kk (kapp_args (lift e))) = some (lift major). Chain via lift_at_kapp_args + list_map_drop + list_map_head + opt_map_some. The level-3 reconstruction of the LIFT E-core; lift analogue of iota_major_inst, no guard. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "kapp_args".to_string(),
                    "list_drop".to_string(),
                    "list_head".to_string(),
                    "opt_map".to_string(),
                    "lift_at".to_string(),
                    "lift_at_kapp_args".to_string(),
                    "list_map_drop".to_string(),
                    "list_map_head".to_string(),
                    "opt_map_some".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // 7. iota_lift_commutes: THE LIFT E-core keystone. lift_at commutes past the
        // directed iota step:
        //   RecEnvLiftClosed env -> iota_reduct env e = some e'
        //     -> iota_reduct env (lift_at e c a) = some (lift_at e' c a).
        // Mirror of iota_subst_commutes: invert via iota_reduct_some_inv, reconstruct
        // via opt_bind_some_intro 5×. UNCONDITIONALLY: the head-const lookups survive
        // lift (kexpr_const_name_lift, levels 1 & 4), the major survives
        // (iota_major_lift, level 3), the metadata/rule lookups are unchanged (h2, h5),
        // and the reduct slot is closed by iota_reduct_lift_eq (level 6). No const-head
        // guard needed (lift never changes the head).
        {
            let el = "(lift_at e c a)";
            let ml = "(lift_at major c a)";
            let epl = "(lift_at e' c a)";
            let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))";
            let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))";

            // The reduct, parameterized by the e-expr and major-expr (mirrors
            // iota_reduct's def + iota_reduct_some_inv exactly).
            let mk_reduct = |es: &str, ms: &str| -> String {
                format!(
                    "(apply_spine (list_drop (Nat.succ {major_idx}) (kapp_args {es})) \
                     (apply_spine (list_drop (Nat.sub (list_length (kapp_args {ms})) (recrule_num_fields rule)) (kapp_args {ms})) \
                     (apply_spine (list_take {prefix_n} (kapp_args {es})) (recrule_rhs rule))))"
                )
            };
            let reduct_orig = mk_reduct("e", "major");
            let reduct_l_majvar = mk_reduct(el, "major");
            let reduct_l_majlift = mk_reduct(el, ml);

            // The lift-side opt_bind continuations (iota_reduct's def with e:=lift e;
            // f4sub/f5sub carry major:=lift major for the level-4/5 obligations).
            let f5 = format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct_l_majvar})");
            let f4 = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {f5})"
            );
            let f3 = format!(
                "(fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) {f4})"
            );
            let f2 = format!(
                "(fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop {major_idx} (kapp_args {el}))) {f3})"
            );
            let f1 = format!(
                "(fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) {f2})"
            );
            let f5sub =
                format!("(fun (rule : RecRule) => OptionType.some KExpr {reduct_l_majlift})");
            let f4sub = format!(
                "(fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) {f5sub})"
            );

            // Lift-side lookups: heads survive lift (levels 1 & 4); major survives (3).
            let h1l = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {el})) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname) \
                 (kexpr_const_name_lift c a e) h1)"
            );
            let h3l = format!("(iota_major_lift c a e {major_idx} major h3)");
            let h4l = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn {ml})) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) \
                 (kexpr_const_name_lift c a major) h4)"
            );
            // Level-6: some REDUCT_l = some (lift e') via iota_reduct_lift_eq + cong.
            let hf6 = format!(
                "(Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr X) \
                 {reduct_l_majlift} {epl} \
                 (iota_reduct_lift_eq env c a e e' recname meta major cname rule liftclosed h5 h5r))"
            );

            // The nested opt_bind_some_intro chain (outside-in, 5 levels).
            let recon = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {el})) {f1} recname {epl} {h1l} \
                 (opt_bind_some_intro RecMeta KExpr (recmeta_for env recname) {f2} meta {epl} h2 \
                 (opt_bind_some_intro KExpr KExpr (list_head (list_drop {major_idx} (kapp_args {el}))) {f3} {ml} {epl} {h3l} \
                 (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn {ml})) {f4sub} cname {epl} {h4l} \
                 (opt_bind_some_intro RecRule KExpr (recrule_for env recname cname) {f5sub} rule {epl} h5 {hf6}))))"
            );

            // The continuation k passed to iota_reduct_some_inv (binders match kont).
            let kont_lambda = format!(
                "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname)) \
                 (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
                 (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args e))) (OptionType.some KExpr major)) \
                 (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
                 (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
                 (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {reduct_orig}) (OptionType.some KExpr e')) => \
                 {recon})"
            );

            let goal_l = format!(
                "(Eq (OptionType KExpr) (iota_reduct env {el}) (OptionType.some KExpr {epl}))"
            );

            let value = format!(
                "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (c : Nat) (a : Nat) \
                 (liftclosed : RecEnvLiftClosed env) \
                 (h : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e')) => \
                 iota_reduct_some_inv env e e' {goal_l} h {kont_lambda}"
            );

            self.add_definition(SpecDefinition {
                name: "iota_lift_commutes".to_string(),
                type_src: concat!(
                    "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (c : Nat) (a : Nat), ",
                    "RecEnvLiftClosed env -> ",
                    "Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e') -> ",
                    "Eq (OptionType KExpr) (iota_reduct env (lift_at e c a)) (OptionType.some KExpr (lift_at e' c a))"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: "LIFT E-core keystone: lift_at commutes past the directed iota step. From a lift-closed env and iota_reduct env e = some e', derive iota_reduct env (lift e) = some (lift e'). Inverts via iota_reduct_some_inv then reconstructs via opt_bind_some_intro 5× (const-head lookups survive lift via kexpr_const_name_lift, major survives via iota_major_lift, metadata/rule unchanged, reduct slot closed by iota_reduct_lift_eq). UNCONDITIONAL (no head-const guard). The full-relation par_lift_full_c iota arm consumes this. DerivedProved, zero axiom_deps. Part of #2859 (LIFT E-core).".to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_reduct".to_string(),
                    "iota_reduct_some_inv".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "iota_reduct_lift_eq".to_string(),
                    "iota_major_lift".to_string(),
                    "kexpr_const_name_lift".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        self.add_strong_induction_primitives()?;

        Ok(())
    }

    /// Strong (well-founded, size) induction over `Nat`, the recursion primitive
    /// the FULL single-step confluence diamond `par_strips_c_full` needs to supply
    /// itself a sub-diamond on a strictly-smaller subterm (the (b2) over-applied
    /// (iota,app) case where `par_reduces_c.rec`'s atomic iota arm gives no IH).
    ///
    /// Built with NO axiom: a small tower of `Nat`/`Lt` no-confusion + bridge
    /// lemmas (`Lt` is `Type`-valued so `Lt.rec` large-eliminates into the
    /// `Type`-valued motive `P`), then `Nat.rec` accumulator recursion bounded by
    /// `Lt`. Part of #2859 (Increment F capstone).
    fn add_strong_induction_primitives(&mut self) -> Result<(), SpecError> {
        // ---------------------------------------------------------------
        // Nat no-confusion (Type-valued), built from a Nat.rec discriminator.
        // ---------------------------------------------------------------

        // nat_zero_ne_succ : Eq 0 (succ a) is absurd (CPS into any Type). The
        // discriminator D reduces to Nat at 0 and Empty at succ; transport the
        // canonical inhabitant (Nat.zero : D 0) along the equation to land in
        // D (succ a) = Empty, then Empty.rec into C.
        self.add_definition(SpecDefinition {
            name: "nat_zero_ne_succ".to_string(),
            type_src: "forall (a : Nat) (C : Type), Eq Nat Nat.zero (Nat.succ a) -> C".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (C : Type) (h : Eq Nat Nat.zero (Nat.succ a)) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Eq.substType Nat ",
                    "(fun (z : Nat) => Nat.rec (fun (_ : Nat) => Type) Nat (fun (_ : Nat) (_ : Type) => Empty) z) ",
                    "Nat.zero (Nat.succ a) h Nat.zero)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Nat no-confusion: Eq 0 (succ a) is absurd, CPS-eliminated into any Type C. The Nat.rec ",
                "discriminator reduces to Nat at 0 and Empty at succ; transport the inhabitant (Nat.zero : D 0) ",
                "along the equation to D (succ a) = Empty, then Empty.rec. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F capstone, strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_succ_inj : Eq (succ a) (succ b) -> Eq a b, via Eq.cong with Nat.pred
        // (pred reduces on succ, so pred (succ a) = a definitionally).
        self.add_definition(SpecDefinition {
            name: "nat_succ_inj".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Eq Nat (Nat.succ a) (Nat.succ b) -> Eq Nat a b"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (h : Eq Nat (Nat.succ a) (Nat.succ b)) => ",
                    "Eq.cong Nat Nat (fun (z : Nat) => Nat.pred z) (Nat.succ a) (Nat.succ b) h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Nat successor injectivity: Eq (succ a) (succ b) -> Eq a b, via Eq.cong with Nat.pred ",
                "(pred (succ a) reduces to a). DerivedProved, zero axiom_deps. Part of #2859 (Increment F ",
                "capstone, strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Nat.pred".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ---------------------------------------------------------------
        // Lt foundation (Type-valued, so Lt.rec large-eliminates).
        // ---------------------------------------------------------------

        // lt_zero_absurd : Lt j 0 is absurd (CPS into any Type). Self-contained
        // (does NOT depend on not_lt_zero, which is registered in a LATER stage):
        // Lt.rec with an inline Nat.rec discriminator motive (Empty at y=0, Nat at
        // y=succ). Both Lt constructors target y = succ _, so each arm yields
        // Nat.zero : Nat; at the target Lt j 0 the motive evaluates to Empty.
        self.add_definition(SpecDefinition {
            name: "lt_zero_absurd".to_string(),
            type_src: "forall (j : Nat) (C : Type), Lt j Nat.zero -> C".to_string(),
            value_src: Some(
                concat!(
                    "fun (j : Nat) (C : Type) (h : Lt j Nat.zero) => ",
                    "Empty.rec (fun (_ : Empty) => C) ",
                    "(Lt.rec ",
                    "(fun (x : Nat) (y : Nat) (_ : Lt x y) => ",
                    "Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat) y) ",
                    "(fun (m : Nat) => Nat.zero) ",
                    "(fun (k : Nat) (mm : Nat) (_hkm : Lt k mm) (_ih : Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat) mm) => Nat.zero) ",
                    "j Nat.zero h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt j 0 is absurd, CPS-eliminated into any Type C. Self-contained (independent of not_lt_zero, ",
                "registered in a later stage): Lt.rec with an inline Nat.rec discriminator (Empty at y=0, Nat at ",
                "y=succ); both Lt constructors target succ indices so each arm yields Nat.zero, and at the target ",
                "Lt j 0 the motive is Empty. DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone, ",
                "strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.rec".to_string(),
                "Nat.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_succ_self : Lt n (succ n) for all n. Nat.rec on n: base Lt 0 (succ 0)
        // via Lt.zero_lt_succ; succ via Lt.succ_lt_succ on the IH.
        self.add_definition(SpecDefinition {
            name: "lt_succ_self".to_string(),
            type_src: "forall (n : Nat), Lt n (Nat.succ n)".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) => ",
                    "Nat.rec (fun (n0 : Nat) => Lt n0 (Nat.succ n0)) ",
                    "(Lt.zero_lt_succ Nat.zero) ",
                    "(fun (m : Nat) (ih : Lt m (Nat.succ m)) => ",
                    "Lt.succ_lt_succ m (Nat.succ m) ih) ",
                    "n"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt n (succ n) for all n: Nat.rec on n (Lt.zero_lt_succ base, Lt.succ_lt_succ succ). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone, strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.zero_lt_succ".to_string(),
                "Lt.succ_lt_succ".to_string(),
                "Nat.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_succ_succ_to_lt : Lt (succ a) (succ b) -> Lt a b. Lt.rec with an
        // equation-indexed motive (the standard inversion): the zero_lt_succ arm is
        // absurd (forces Eq 0 (succ a), nat_zero_ne_succ); the succ_lt_succ arm
        // transports the carried sub-Lt across the two succ-injective equations.
        self.add_definition(SpecDefinition {
            name: "lt_succ_succ_to_lt".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt (Nat.succ a) (Nat.succ b) -> Lt a b"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (h : Lt (Nat.succ a) (Nat.succ b)) => ",
                    "Lt.rec ",
                    "(fun (x : Nat) (y : Nat) (_ : Lt x y) => ",
                    "forall (a0 : Nat) (b0 : Nat), Eq Nat x (Nat.succ a0) -> Eq Nat y (Nat.succ b0) -> Lt a0 b0) ",
                    // zero_lt_succ arm: x = 0, so Eq 0 (succ a0) is absurd.
                    "(fun (m : Nat) (a0 : Nat) (b0 : Nat) ",
                    "(ex : Eq Nat Nat.zero (Nat.succ a0)) (_ey : Eq Nat (Nat.succ m) (Nat.succ b0)) => ",
                    "nat_zero_ne_succ a0 (Lt a0 b0) ex) ",
                    // succ_lt_succ arm: x = succ a', y = succ b', hh : Lt a' b'.
                    "(fun (a' : Nat) (b' : Nat) (hh : Lt a' b') ",
                    "(_ih : forall (a0 : Nat) (b0 : Nat), Eq Nat a' (Nat.succ a0) -> Eq Nat b' (Nat.succ b0) -> Lt a0 b0) ",
                    "(a0 : Nat) (b0 : Nat) ",
                    "(ex : Eq Nat (Nat.succ a') (Nat.succ a0)) (ey : Eq Nat (Nat.succ b') (Nat.succ b0)) => ",
                    // transport hh : Lt a' b' to Lt a0 b0 via the two succ-injective eqs.
                    "Eq.substType Nat (fun (z : Nat) => Lt a0 z) b' b0 (nat_succ_inj b' b0 ey) ",
                    "(Eq.substType Nat (fun (z : Nat) => Lt z b') a' a0 (nat_succ_inj a' a0 ex) hh)) ",
                    "(Nat.succ a) (Nat.succ b) h ",
                    "a b (Eq.refl Nat (Nat.succ a)) (Eq.refl Nat (Nat.succ b))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt successor stripping: Lt (succ a) (succ b) -> Lt a b. Lt.rec with an equation-indexed ",
                "motive; the zero_lt_succ arm is absurd (nat_zero_ne_succ on Eq 0 (succ a0)), the succ_lt_succ ",
                "arm transports the carried sub-Lt across the two succ-injective equations (nat_succ_inj). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone, strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.rec".to_string(),
                "nat_zero_ne_succ".to_string(),
                "nat_succ_inj".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_strict_split : Lt a b -> (succ a < b) or (succ a = b), CPS into any
        // Type C. Lt.rec on the proof with motive
        //   M a b _ := forall C, (Lt (succ a) b -> C) -> (Eq (succ a) b -> C) -> C.
        // zero_lt_succ m: decide on m via Nat.rec (m=0 -> Eq 1 1 refl; m=succ ->
        //   Lt 1 (succ (succ m')) via succ_lt_succ). succ_lt_succ arm: route through
        //   the inner IH, lifting each branch by one succ (succ_lt_succ / Eq.cong succ).
        self.add_definition(SpecDefinition {
            name: "nat_strict_split".to_string(),
            type_src: concat!(
                "forall (a : Nat) (b : Nat), Lt a b -> ",
                "forall (C : Type), (Lt (Nat.succ a) b -> C) -> (Eq Nat (Nat.succ a) b -> C) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (h : Lt a b) => ",
                    "Lt.rec ",
                    "(fun (x : Nat) (y : Nat) (_ : Lt x y) => ",
                    "forall (C : Type), (Lt (Nat.succ x) y -> C) -> (Eq Nat (Nat.succ x) y -> C) -> C) ",
                    // zero_lt_succ m : Lt 0 (succ m). Need split of Lt 0 (succ m) into
                    //   Lt 1 (succ m) or Eq 1 (succ m). Decide on m.
                    "(fun (m : Nat) => ",
                    "Nat.rec (fun (m0 : Nat) => ",
                    "forall (C : Type), (Lt (Nat.succ Nat.zero) (Nat.succ m0) -> C) -> (Eq Nat (Nat.succ Nat.zero) (Nat.succ m0) -> C) -> C) ",
                    // m0 = 0: Eq 1 1 via refl.
                    "(fun (C : Type) (_kl : Lt (Nat.succ Nat.zero) (Nat.succ Nat.zero) -> C) ",
                    "(ke : Eq Nat (Nat.succ Nat.zero) (Nat.succ Nat.zero) -> C) => ke (Eq.refl Nat (Nat.succ Nat.zero))) ",
                    // m0 = succ m': Lt 1 (succ (succ m')) via succ_lt_succ 0 (succ m') (zero_lt_succ m').
                    "(fun (m' : Nat) (_ihm : forall (C : Type), (Lt (Nat.succ Nat.zero) (Nat.succ m') -> C) -> (Eq Nat (Nat.succ Nat.zero) (Nat.succ m') -> C) -> C) ",
                    "(C : Type) (kl : Lt (Nat.succ Nat.zero) (Nat.succ (Nat.succ m')) -> C) ",
                    "(_ke : Eq Nat (Nat.succ Nat.zero) (Nat.succ (Nat.succ m')) -> C) => ",
                    "kl (Lt.succ_lt_succ Nat.zero (Nat.succ m') (Lt.zero_lt_succ m'))) ",
                    "m) ",
                    // succ_lt_succ a' b' hh : Lt (succ a') (succ b'), inner IH ih.
                    "(fun (a' : Nat) (b' : Nat) (_hh : Lt a' b') ",
                    "(ih : forall (C : Type), (Lt (Nat.succ a') b' -> C) -> (Eq Nat (Nat.succ a') b' -> C) -> C) ",
                    "(C : Type) (kl : Lt (Nat.succ (Nat.succ a')) (Nat.succ b') -> C) ",
                    "(ke : Eq Nat (Nat.succ (Nat.succ a')) (Nat.succ b') -> C) => ",
                    "ih C ",
                    "(fun (hlt : Lt (Nat.succ a') b') => kl (Lt.succ_lt_succ (Nat.succ a') b' hlt)) ",
                    "(fun (heq : Eq Nat (Nat.succ a') b') => ke (Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) (Nat.succ a') b' heq))) ",
                    "a b h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Strict trichotomy half: Lt a b splits (CPS into any Type C) into Lt (succ a) b or ",
                "Eq (succ a) b. Lt.rec on the proof; the zero_lt_succ arm decides on the bound via Nat.rec, the ",
                "succ_lt_succ arm routes through the inner IH lifting each branch by one succ. The Type-valued ",
                "case-split the strong-induction accumulator needs. DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment F capstone, strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.rec".to_string(),
                "Lt.zero_lt_succ".to_string(),
                "Lt.succ_lt_succ".to_string(),
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ---------------------------------------------------------------
        // The strong-recursion primitive (Nat.rec accumulator bounded by Lt).
        // ---------------------------------------------------------------

        // nat_lt_rec_bounded : course-of-values bounded recursion. Nat.rec on the
        // bound n with motive Q n := forall j, Lt j (succ n) -> P j. base (n=0):
        // Lt j 1 forces j=0 (strict_split: the Lt-arm is absurd via
        // lt_succ_succ_to_lt + lt_zero_absurd, the Eq-arm gives j=0), and P 0 =
        // step 0 (vacuous lt_zero_absurd discharger). step (succ n): Lt j (succ
        // (succ n)) splits into Lt j (succ n) (-> ih) or j = succ n (-> P (succ n)
        // = step (succ n) ih, the strong IH at k = succ n).
        self.add_definition(SpecDefinition {
            name: "nat_lt_rec_bounded".to_string(),
            type_src: concat!(
                "forall (P : Nat -> Type), ",
                "(forall (k : Nat), (forall (j : Nat), Lt j k -> P j) -> P k) -> ",
                "forall (n : Nat) (j : Nat), Lt j (Nat.succ n) -> P j"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (P : Nat -> Type) ",
                    "(step : forall (k : Nat), (forall (j : Nat), Lt j k -> P j) -> P k) => ",
                    "Nat.rec ",
                    "(fun (n0 : Nat) => forall (j : Nat), Lt j (Nat.succ n0) -> P j) ",
                    // base n=0: forall j, Lt j (succ 0) -> P j.
                    "(fun (j : Nat) (hlt : Lt j (Nat.succ Nat.zero)) => ",
                    "nat_strict_split j (Nat.succ Nat.zero) hlt (P j) ",
                    // Lt (succ j) 1 arm: absurd.
                    "(fun (hL : Lt (Nat.succ j) (Nat.succ Nat.zero)) => ",
                    "lt_zero_absurd j (P j) (lt_succ_succ_to_lt j Nat.zero hL)) ",
                    // Eq (succ j) 1 arm: j = 0, transport P 0.
                    "(fun (hE : Eq Nat (Nat.succ j) (Nat.succ Nat.zero)) => ",
                    "Eq.substType Nat P Nat.zero j ",
                    "(Eq.symm Nat j Nat.zero (nat_succ_inj j Nat.zero hE)) ",
                    "(step Nat.zero (fun (i : Nat) (hi : Lt i Nat.zero) => lt_zero_absurd i (P i) hi)))) ",
                    // step succ n: ih : forall j, Lt j (succ n) -> P j.
                    "(fun (n : Nat) (ih : forall (j : Nat), Lt j (Nat.succ n) -> P j) ",
                    "(j : Nat) (hlt : Lt j (Nat.succ (Nat.succ n))) => ",
                    "nat_strict_split j (Nat.succ (Nat.succ n)) hlt (P j) ",
                    // Lt (succ j) (succ (succ n)) arm: -> Lt j (succ n) -> ih.
                    "(fun (hL : Lt (Nat.succ j) (Nat.succ (Nat.succ n))) => ",
                    "ih j (lt_succ_succ_to_lt j (Nat.succ n) hL)) ",
                    // Eq (succ j) (succ (succ n)) arm: j = succ n, transport P (succ n) = step (succ n) ih.
                    "(fun (hE : Eq Nat (Nat.succ j) (Nat.succ (Nat.succ n))) => ",
                    "Eq.substType Nat P (Nat.succ n) j ",
                    "(Eq.symm Nat j (Nat.succ n) (nat_succ_inj j (Nat.succ n) hE)) ",
                    "(step (Nat.succ n) ih)))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Course-of-values bounded recursion: from the strong-induction step (P k from P-below-k), ",
                "build forall n j, Lt j (succ n) -> P j. Nat.rec on the bound n; the base (n=0) forces j=0 ",
                "(strict_split: Lt-arm absurd via lt_succ_succ_to_lt + lt_zero_absurd; Eq-arm gives j=0) and ",
                "P 0 = step 0 (vacuous discharger); the succ step splits Lt j (succ (succ n)) into the recursive ",
                "ih or j = succ n (P (succ n) = step (succ n) ih, the strong IH at k = succ n). The bridge from ",
                "the Type-valued strict-split to the strong recursor. DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment F capstone, strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.rec".to_string(),
                "nat_strict_split".to_string(),
                "lt_succ_succ_to_lt".to_string(),
                "lt_zero_absurd".to_string(),
                "nat_succ_inj".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_strong_rec : strong induction on Nat. Specialize nat_lt_rec_bounded at
        // the bound n with the seed Lt n (succ n) (lt_succ_self n).
        self.add_definition(SpecDefinition {
            name: "nat_strong_rec".to_string(),
            type_src: concat!(
                "forall (P : Nat -> Type), ",
                "(forall (k : Nat), (forall (j : Nat), Lt j k -> P j) -> P k) -> ",
                "forall (n : Nat), P n"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (P : Nat -> Type) ",
                    "(step : forall (k : Nat), (forall (j : Nat), Lt j k -> P j) -> P k) ",
                    "(n : Nat) => ",
                    "nat_lt_rec_bounded P step n n (lt_succ_self n)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Strong (well-founded) induction on Nat: P holds at every n given that P k follows from P at ",
                "every j < k. Specialize nat_lt_rec_bounded at the bound n with the seed Lt n (succ n) ",
                "(lt_succ_self). The recursion primitive the FULL single-step confluence diamond ",
                "par_strips_c_full strong-inducts on (over expr_size) to supply itself the sub-diamond on a ",
                "strictly-smaller subterm that par_reduces_c.rec's atomic iota arm cannot. DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment F capstone, strong-induction primitive)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "nat_lt_rec_bounded".to_string(),
                "lt_succ_self".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_expr_size_decrease_lemmas()?;

        Ok(())
    }

    /// `expr_size`-decrease facts (over `Lt`) for the subterm positions the FULL
    /// single-step diamond `par_strips_c_full` recurses into, plus the small `Lt`
    /// toolkit (`lt_succ_weaken`, `lt_trans`, `lt_add_succ_left/right`) they compose
    /// from. All defeq-driven via the `expr_size` / `Nat.add` reduction rules
    /// (`expr_size (app f a) ≡ succ (add (size f) (size a))`, `add a 0 ≡ a`,
    /// `add a (succ m) ≡ succ (add a m)`). No axiom. Part of #2859 (Increment F capstone).
    fn add_expr_size_decrease_lemmas(&mut self) -> Result<(), SpecError> {
        // lt_succ_weaken : Lt a c -> Lt a (succ c). Lt.rec on the proof; motive
        //   M x y _ := Lt x (succ y). zero_lt_succ m -> Lt.zero_lt_succ (succ m);
        //   succ_lt_succ arm lifts the IH by one succ on the right.
        self.add_definition(SpecDefinition {
            name: "lt_succ_weaken".to_string(),
            type_src: "forall (a : Nat) (c : Nat), Lt a c -> Lt a (Nat.succ c)".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (c : Nat) (h : Lt a c) => ",
                    "Lt.rec ",
                    "(fun (x : Nat) (y : Nat) (_ : Lt x y) => Lt x (Nat.succ y)) ",
                    "(fun (m : Nat) => Lt.zero_lt_succ (Nat.succ m)) ",
                    "(fun (a' : Nat) (b' : Nat) (_hh : Lt a' b') (ih : Lt a' (Nat.succ b')) => ",
                    "Lt.succ_lt_succ a' (Nat.succ b') ih) ",
                    "a c h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt weakening on the right: Lt a c -> Lt a (succ c). Lt.rec on the proof; zero_lt_succ -> ",
                "Lt.zero_lt_succ (succ m), succ_lt_succ lifts the IH by one succ. DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment F capstone, expr_size decrease toolkit)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.rec".to_string(),
                "Lt.zero_lt_succ".to_string(),
                "Lt.succ_lt_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_trans : Lt a b -> Lt b c -> Lt a c. Lt.rec on the SECOND proof with
        //   motive M x y _ := forall a, Lt a x -> Lt a y. zero_lt_succ -> the
        //   Lt a 0 hypothesis is absurd; succ_lt_succ -> split Lt a (succ b') via
        //   nat_strict_split (the Lt-arm strips a succ then applies the IH + weaken;
        //   the Eq-arm transports the carried sub-Lt then weakens).
        self.add_definition(SpecDefinition {
            name: "lt_trans".to_string(),
            type_src: "forall (a : Nat) (b : Nat) (c : Nat), Lt a b -> Lt b c -> Lt a c".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) (hab : Lt a b) (hbc : Lt b c) => ",
                    "Lt.rec ",
                    "(fun (x : Nat) (y : Nat) (_ : Lt x y) => forall (a0 : Nat), Lt a0 x -> Lt a0 y) ",
                    // zero_lt_succ m : Lt 0 (succ m). Need forall a0, Lt a0 0 -> Lt a0 (succ m).
                    "(fun (m : Nat) (a0 : Nat) (h0 : Lt a0 Nat.zero) => lt_zero_absurd a0 (Lt a0 (Nat.succ m)) h0) ",
                    // succ_lt_succ b' c' h : Lt (succ b') (succ c'), ih : forall a0, Lt a0 b' -> Lt a0 c'.
                    "(fun (b' : Nat) (c' : Nat) (hh : Lt b' c') ",
                    "(ih : forall (a0 : Nat), Lt a0 b' -> Lt a0 c') ",
                    "(a0 : Nat) (hab0 : Lt a0 (Nat.succ b')) => ",
                    "nat_strict_split a0 (Nat.succ b') hab0 (Lt a0 (Nat.succ c')) ",
                    // Lt (succ a0) (succ b') arm: a0 < b' -> ih -> weaken.
                    "(fun (hL : Lt (Nat.succ a0) (Nat.succ b')) => ",
                    "lt_succ_weaken a0 c' (ih a0 (lt_succ_succ_to_lt a0 b' hL))) ",
                    // Eq (succ a0) (succ b') arm: a0 = b', transport hh then weaken.
                    "(fun (hE : Eq Nat (Nat.succ a0) (Nat.succ b')) => ",
                    "lt_succ_weaken a0 c' ",
                    "(Eq.substType Nat (fun (z : Nat) => Lt z c') b' a0 ",
                    "(Eq.symm Nat a0 b' (nat_succ_inj a0 b' hE)) hh))) ",
                    "b c hbc a hab"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Transitivity of Lt: Lt a b -> Lt b c -> Lt a c. Lt.rec on the second proof with motive ",
                "forall a, Lt a x -> Lt a y; the zero_lt_succ arm discharges the absurd Lt a 0 hypothesis ",
                "(lt_zero_absurd), the succ_lt_succ arm splits Lt a (succ b') via nat_strict_split (Lt-arm: ",
                "strip-succ + ih + weaken; Eq-arm: transport + weaken). DerivedProved, zero axiom_deps. Part of ",
                "#2859 (Increment F capstone, expr_size decrease toolkit)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Lt.rec".to_string(),
                "nat_strict_split".to_string(),
                "lt_succ_succ_to_lt".to_string(),
                "lt_succ_weaken".to_string(),
                "lt_zero_absurd".to_string(),
                "nat_succ_inj".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_add_succ_left : Lt a (succ (add a b)). Nat.rec on b: b=0 reduces
        //   (add a 0 ≡ a) to Lt a (succ a) = lt_succ_self; b=succ m reduces
        //   (add a (succ m) ≡ succ (add a m)) to Lt a (succ (succ (add a m))),
        //   from the IH via lt_succ_weaken.
        self.add_definition(SpecDefinition {
            name: "lt_add_succ_left".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt a (Nat.succ (Nat.add a b))".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) => ",
                    "Nat.rec (fun (b0 : Nat) => Lt a (Nat.succ (Nat.add a b0))) ",
                    "(lt_succ_self a) ",
                    "(fun (m : Nat) (ih : Lt a (Nat.succ (Nat.add a m))) => ",
                    "lt_succ_weaken a (Nat.succ (Nat.add a m)) ih) ",
                    "b"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt a (succ (add a b)) for all a, b. Nat.rec on b; b=0 reduces (add a 0 ≡ a) to ",
                "Lt a (succ a) = lt_succ_self, b=succ m reduces (add a (succ m) ≡ succ (add a m)) and weakens the ",
                "IH via lt_succ_weaken. The left-summand size-decrease for app/binder fst positions. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment F capstone, expr_size decrease toolkit)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.rec".to_string(),
                "Nat.add".to_string(),
                "lt_succ_self".to_string(),
                "lt_succ_weaken".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // lt_add_succ_right : Lt b (succ (add a b)). Nat.rec on b: b=0 reduces
        //   (add a 0 ≡ a) to Lt 0 (succ a) = Lt.zero_lt_succ a; b=succ m reduces
        //   (add a (succ m) ≡ succ (add a m)) to Lt (succ m) (succ (succ (add a m))),
        //   from the IH (Lt m (succ (add a m))) via Lt.succ_lt_succ.
        self.add_definition(SpecDefinition {
            name: "lt_add_succ_right".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Lt b (Nat.succ (Nat.add a b))".to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) => ",
                    "Nat.rec (fun (b0 : Nat) => Lt b0 (Nat.succ (Nat.add a b0))) ",
                    "(Lt.zero_lt_succ a) ",
                    "(fun (m : Nat) (ih : Lt m (Nat.succ (Nat.add a m))) => ",
                    "Lt.succ_lt_succ m (Nat.succ (Nat.add a m)) ih) ",
                    "b"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt b (succ (add a b)) for all a, b. Nat.rec on b; b=0 reduces (add a 0 ≡ a) to ",
                "Lt 0 (succ a) = Lt.zero_lt_succ, b=succ m reduces (add a (succ m) ≡ succ (add a m)) and applies ",
                "Lt.succ_lt_succ to the IH. The right-summand size-decrease for app/binder snd positions. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F capstone, expr_size decrease toolkit)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.rec".to_string(),
                "Nat.add".to_string(),
                "Lt.zero_lt_succ".to_string(),
                "Lt.succ_lt_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The six direct subterm size-decrease lemmas. Each is a defeq corollary of
        // lt_add_succ_left/right at expr_size arguments, since
        //   expr_size (app f a) ≡ succ (add (expr_size f) (expr_size a))   (and lam/pi alike).
        for (name, head, which, label) in [
            ("size_app_fst", "KExpr.app", "L", "head of an application"),
            (
                "size_app_snd",
                "KExpr.app",
                "R",
                "argument of an application",
            ),
            ("size_lam_fst", "KExpr.lam", "L", "type of a lambda"),
            ("size_lam_snd", "KExpr.lam", "R", "body of a lambda"),
            ("size_pi_fst", "KExpr.pi", "L", "domain of a pi"),
            ("size_pi_snd", "KExpr.pi", "R", "body of a pi"),
        ] {
            let (lemma, sub) = match which {
                "L" => ("lt_add_succ_left", "u"),
                _ => ("lt_add_succ_right", "v"),
            };
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall (u : KExpr) (v : KExpr), Lt (expr_size {sub}) (expr_size ({head} u v))",
                    sub = sub,
                    head = head,
                ),
                value_src: Some(format!(
                    "fun (u : KExpr) (v : KExpr) => {lemma} (expr_size u) (expr_size v)",
                    lemma = lemma,
                )),
                is_axiom: false,
                description: format!(
                    concat!(
                        "expr_size decrease for the {label}: Lt (expr_size sub) (expr_size ({head} u v)). Defeq ",
                        "corollary of {lemma} at the two child sizes, since expr_size ({head} u v) reduces to ",
                        "succ (add (expr_size u) (expr_size v)). DerivedProved, zero axiom_deps. Part of #2859 ",
                        "(Increment F capstone, expr_size decrease)."
                    ),
                    label = label,
                    head = head,
                    lemma = lemma,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "Lt".to_string(),
                    "expr_size".to_string(),
                    lemma.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // size_proj_sub: expr_size decrease for the scrutinee of a projection
        // (proj/lit fragment rung). expr_size (proj s i sub) ≡ succ (expr_size sub),
        // so Lt (expr_size sub) (expr_size (proj s i sub)) is lt_succ_self at
        // expr_size sub (defeq).
        self.add_definition(SpecDefinition {
            name: "size_proj_sub".to_string(),
            type_src: concat!(
                "forall (s : Name) (i : Nat) (sub : KExpr), ",
                "Lt (expr_size sub) (expr_size (KExpr.proj s i sub))"
            )
            .to_string(),
            value_src: Some(
                "fun (s : Name) (i : Nat) (sub : KExpr) => lt_succ_self (expr_size sub)"
                    .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "expr_size decrease for the scrutinee of a projection: ",
                "Lt (expr_size sub) (expr_size (KExpr.proj s i sub)). Defeq corollary of ",
                "lt_succ_self, since expr_size (proj s i sub) reduces to succ (expr_size sub). ",
                "DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "expr_size".to_string(),
                "lt_succ_self".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Let-promotion size-decrease trio (task #28) ──────────────────
        // expr_size (let_ u v w) ≡ succ (add Su (add Sv Sw)), so the three
        // component decreases need the middle/last-of-nested-add analogues of
        // lt_add_succ_left/right. Nat.add recurses on its SECOND argument, so
        // neither nested shape reduces on a prefix Nat.rec; instead both are
        // Eq.substType transports of the binary lemmas along assoc/comm
        // rewrites of the nested sum.
        self.add_definition(SpecDefinition {
            name: "lt_add_succ_mid".to_string(),
            type_src:
                "forall (a : Nat) (b : Nat) (c : Nat), Lt b (Nat.succ (Nat.add a (Nat.add b c)))"
                    .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) => ",
                    "Eq.substType Nat (fun (z : Nat) => Lt b (Nat.succ z)) ",
                    "(Nat.add b (Nat.add a c)) ",
                    "(Nat.add a (Nat.add b c)) ",
                    "(Eq.trans Nat ",
                    "(Nat.add b (Nat.add a c)) ",
                    "(Nat.add (Nat.add b a) c) ",
                    "(Nat.add a (Nat.add b c)) ",
                    "(Eq.symm Nat (Nat.add (Nat.add b a) c) (Nat.add b (Nat.add a c)) ",
                    "(nat_add_assoc b a c)) ",
                    "(Eq.trans Nat ",
                    "(Nat.add (Nat.add b a) c) ",
                    "(Nat.add (Nat.add a b) c) ",
                    "(Nat.add a (Nat.add b c)) ",
                    "(Eq.cong Nat Nat (fun (x : Nat) => Nat.add x c) ",
                    "(Nat.add b a) (Nat.add a b) (nat_add_comm b a)) ",
                    "(nat_add_assoc a b c))) ",
                    "(lt_add_succ_left b (Nat.add a c))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt b (succ (a + (b + c))): the middle summand of a nested add is below the succ ",
                "of the total. Eq.substType transport of lt_add_succ_left b (a+c) along ",
                "b+(a+c) = (b+a)+c = (a+b)+c = a+(b+c) (symm assoc, comm congruence, assoc). ",
                "DerivedProved, zero axiom_deps. Part of the let-promotion surgery (task #28)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.add".to_string(),
                "Eq.substType".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.cong".to_string(),
                "nat_add_assoc".to_string(),
                "nat_add_comm".to_string(),
                "lt_add_succ_left".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "lt_add_succ_last".to_string(),
            type_src:
                "forall (a : Nat) (b : Nat) (c : Nat), Lt c (Nat.succ (Nat.add a (Nat.add b c)))"
                    .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : Nat) (b : Nat) (c : Nat) => ",
                    "Eq.substType Nat (fun (z : Nat) => Lt c (Nat.succ z)) ",
                    "(Nat.add (Nat.add a b) c) ",
                    "(Nat.add a (Nat.add b c)) ",
                    "(nat_add_assoc a b c) ",
                    "(lt_add_succ_right (Nat.add a b) c)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Lt c (succ (a + (b + c))): the last summand of a nested add is below the succ ",
                "of the total. Eq.substType transport of lt_add_succ_right (a+b) c along ",
                "nat_add_assoc. DerivedProved, zero axiom_deps. Part of the let-promotion ",
                "surgery (task #28)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Lt".to_string(),
                "Nat.add".to_string(),
                "Eq.substType".to_string(),
                "nat_add_assoc".to_string(),
                "lt_add_succ_right".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The three direct let-subterm size-decrease lemmas, defeq corollaries
        // at expr_size arguments since
        //   expr_size (let_ u v w) ≡ succ (add (expr_size u) (add (expr_size v) (expr_size w))).
        for (name, lemma, comp, label) in [
            ("size_let_fst", "lt_add_succ_left", "u", "type of a let"),
            ("size_let_snd", "lt_add_succ_mid", "v", "value of a let"),
            ("size_let_thd", "lt_add_succ_last", "w", "body of a let"),
        ] {
            let value = if name == "size_let_fst" {
                // lt_add_succ_left Su (add Sv Sw) : Lt Su (succ (add Su (add Sv Sw))).
                "fun (u : KExpr) (v : KExpr) (w : KExpr) => lt_add_succ_left (expr_size u) (Nat.add (expr_size v) (expr_size w))".to_string()
            } else {
                format!(
                    "fun (u : KExpr) (v : KExpr) (w : KExpr) => {lemma} (expr_size u) (expr_size v) (expr_size w)",
                    lemma = lemma,
                )
            };
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall (u : KExpr) (v : KExpr) (w : KExpr), Lt (expr_size {comp}) (expr_size (KExpr.let_ u v w))",
                    comp = comp,
                ),
                value_src: Some(value),
                is_axiom: false,
                description: format!(
                    concat!(
                        "expr_size decrease for the {label}: Lt (expr_size sub) (expr_size (let_ u v w)). ",
                        "Defeq corollary of {lemma} at the three child sizes. DerivedProved, zero ",
                        "axiom_deps. Part of the let-promotion surgery (task #28)."
                    ),
                    label = label,
                    lemma = lemma,
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "Lt".to_string(),
                    "expr_size".to_string(),
                    lemma.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }
}
