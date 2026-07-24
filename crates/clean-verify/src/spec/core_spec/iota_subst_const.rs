// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment E (#2859 computational-iota/delta track): the CONST-HEAD-GUARDED
//! commutations — the crux of E-core.
//!
//! `kapp_fn`/`kapp_args` do NOT commute with `instantiate_at` unconditionally (a
//! bvar spine-head can be replaced by a complex term, changing the spine). But a
//! genuine iota redex is `const`-headed, and `instantiate_at` leaves `const`
//! fixed. So the commutations hold under the guard that the spine head is a
//! const, stated as `kexpr_const_name (kapp_fn e) = some nm`. This is exactly the
//! witness `opt_bind_some_inv` delivers when inverting `iota_reduct`'s first
//! level, so E-core has the guard in hand.
//!
//! The guard discharges the 4 non-`const` `KExpr.rec` arms for free: in a
//! sort/bvar/lam/pi arm the head is structural, `kexpr_const_name (kapp_fn e)`
//! computes to `none`, and the guard `none = some nm` is refuted by
//! `option_none_ne_some` (the Empty-discriminator no-confusion, exactly the
//! `sort_ne_pi` pattern). The `app` arm recurses (guard ≡ propagates since
//! `kapp_fn (app f a) ≡ kapp_fn f`); the `const` arm is the genuine base case
//! (both sides reduce to the same const). Designed by the adversarially-verified
//! design workflow (verdict: guard sound + propagation correct). See
//! `designs/2026-06-14-computational-iota-delta-track.md` (Increment E).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_iota_subst_const(&mut self) -> Result<(), SpecError> {
        // guard(E) : the head of E is the const nm.
        let guard = |e: &str| -> String {
            format!(
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn {e})) (OptionType.some Name nm)"
            )
        };
        // goal(E) : kapp_fn commutes with instantiate_at on E.
        let goal = |e: &str| -> String {
            format!(
                "Eq KExpr (kapp_fn (instantiate_at {e} v d)) (instantiate_at (kapp_fn {e}) v d)"
            )
        };
        // A non-const arm discharged by the guard: the head is structural so
        // kexpr_const_name (kapp_fn ctor) = none, the guard becomes none = some nm,
        // which yields Empty via the opt_is_none discriminator; Empty.rec into the
        // (Prop) goal. (Inlined rather than option_none_ne_some, whose result is in
        // Type — the goal is a Prop, so we eliminate Empty straight into it.)
        let discharge = |ctor: &str| -> String {
            format!(
                "(g : {g}) => Empty.rec (fun (_ : Empty) => {goal}) \
                 (Eq.substType (OptionType Name) (opt_is_none Name) \
                 (OptionType.none Name) (OptionType.some Name nm) g Nat.zero)",
                g = guard(ctor),
                goal = goal(ctor),
            )
        };

        // instantiate_at_kapp_fn_const: under the head-const guard, kapp_fn
        // commutes with instantiate_at. KExpr.rec on e with the guard threaded in
        // the motive.
        let kapp_fn_value = format!(
            concat!(
                "fun (v : KExpr) (d : Nat) (nm : Name) (e : KExpr) => ",
                "KExpr.rec ",
                "(fun (e0 : KExpr) => {g_e0} -> {goal_e0}) ",
                // sort (discharged)
                "(fun (n : Level) {disch_sort}) ",
                // bvar (discharged)
                "(fun (i : Nat) {disch_bvar}) ",
                // app (recursive: guard propagates by defeq, IH on f)
                "(fun (f : KExpr) (a : KExpr) ",
                "(ihf : {g_f} -> {goal_f}) (iha : {g_a} -> {goal_a}) ",
                "(g : {g_appfa}) => ihf g) ",
                // lam (discharged)
                "(fun (ty : KExpr) (b : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihb : {g_b} -> {goal_b}) ",
                "{disch_lam}) ",
                // pi (discharged)
                "(fun (ty : KExpr) (b : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihb : {g_b} -> {goal_b}) ",
                "{disch_pi}) ",
                // const (genuine: both sides reduce to const nm0 us)
                "(fun (nm0 : Name) (us : ListType Level) (g : {g_const}) => ",
                "Eq.refl KExpr (KExpr.const nm0 us)) ",
                // let_ (discharged: a let is its own spine head, never const-headed)
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihval : {g_val} -> {goal_val}) (_ihbody : {g_body} -> {goal_body}) ",
                "{disch_let}) ",
                // proj (discharged: a proj is its own spine head, never const-headed)
                "(fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : {g_sub} -> {goal_sub}) ",
                "{disch_proj}) ",
                // lit (discharged: a lit is never a const-headed spine)
                "(fun (m : Nat) {disch_lit}) ",
                "e"
            ),
            g_e0 = guard("e0"),
            goal_e0 = goal("e0"),
            disch_sort = discharge("(KExpr.sort n)"),
            disch_bvar = discharge("(KExpr.bvar i)"),
            g_f = guard("f"),
            goal_f = goal("f"),
            g_a = guard("a"),
            goal_a = goal("a"),
            g_appfa = guard("(KExpr.app f a)"),
            g_ty = guard("ty"),
            goal_ty = goal("ty"),
            g_b = guard("b"),
            goal_b = goal("b"),
            disch_lam = discharge("(KExpr.lam ty b)"),
            disch_pi = discharge("(KExpr.pi ty b)"),
            g_const = guard("(KExpr.const nm0 us)"),
            g_val = guard("val"),
            goal_val = goal("val"),
            g_body = guard("body"),
            goal_body = goal("body"),
            disch_let = discharge("(KExpr.let_ ty val body)"),
            g_sub = guard("sub"),
            goal_sub = goal("sub"),
            disch_proj = discharge("(KExpr.proj s i sub)"),
            disch_lit = discharge("(KExpr.lit m)"),
        );

        self.add_definition(SpecDefinition {
            name: "instantiate_at_kapp_fn_const".to_string(),
            type_src: format!(
                "forall (v : KExpr) (d : Nat) (nm : Name) (e : KExpr), {g} -> {goal}",
                g = guard("e"),
                goal = goal("e"),
            ),
            value_src: Some(kapp_fn_value),
            is_axiom: false,
            description: concat!(
                "Under the head-const guard (kexpr_const_name (kapp_fn e) = some nm), kapp_fn commutes ",
                "with instantiate_at: kapp_fn (instantiate_at e v d) = instantiate_at (kapp_fn e) v d. ",
                "KExpr.rec on e — const arm genuine (both sides reduce to the same const), app arm ",
                "recursive (guard propagates), sort/bvar/lam/pi arms discharged by the guard via ",
                "option_none_ne_some. DerivedProved, zero axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_fn".to_string(),
                "kexpr_const_name".to_string(),
                "instantiate_at".to_string(),
                "KExpr.rec".to_string(),
                "opt_is_none".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_kapp_args_const: under the head-const guard, kapp_args
        // commutes with instantiate_at up to list_map. Same KExpr.rec structure as
        // kapp_fn, but the app arm is a genuine chain (kapp_args_app +
        // instantiate_at_app + IH + list_map_append) rather than a pure-defeq IH.
        // F := (fun a0 => instantiate_at a0 v d).
        let fmap = "(fun (a0 : KExpr) => instantiate_at a0 v d)";
        // goal_args(E) : kapp_args commutes with instantiate_at (up to list_map).
        let goal_args = |e: &str| -> String {
            format!(
                "Eq (ListType KExpr) (kapp_args (instantiate_at {e} v d)) (list_map {fmap} (kapp_args {e}))"
            )
        };
        let discharge_args = |ctor: &str| -> String {
            format!(
                "(g : {g}) => Empty.rec (fun (_ : Empty) => {goal}) \
                 (Eq.substType (OptionType Name) (opt_is_none Name) \
                 (OptionType.none Name) (OptionType.some Name nm) g Nat.zero)",
                g = guard(ctor),
                goal = goal_args(ctor),
            )
        };
        // The meeting point M for the app arm.
        let meet = format!(
            "(list_append (list_map {fmap} (kapp_args f)) (ListType.cons KExpr (instantiate_at a v d) (ListType.nil KExpr)))"
        );
        let app_arm = format!(
            concat!(
                "(fun (f : KExpr) (a : KExpr) ",
                "(ihf : {g_f} -> {goal_f}) (iha : {g_a} -> {goal_a}) (g : {g_appfa}) => ",
                "Eq.trans (ListType KExpr) ",
                "(kapp_args (instantiate_at (KExpr.app f a) v d)) {meet} (list_map {fmap} (kapp_args (KExpr.app f a))) ",
                // LHS -> M
                "(Eq.trans (ListType KExpr) ",
                "(kapp_args (instantiate_at (KExpr.app f a) v d)) ",
                "(kapp_args (KExpr.app (instantiate_at f v d) (instantiate_at a v d))) {meet} ",
                "(Eq.cong KExpr (ListType KExpr) (fun (X : KExpr) => kapp_args X) ",
                "(instantiate_at (KExpr.app f a) v d) (KExpr.app (instantiate_at f v d) (instantiate_at a v d)) ",
                "(instantiate_at_app f a v d)) ",
                "(Eq.trans (ListType KExpr) ",
                "(kapp_args (KExpr.app (instantiate_at f v d) (instantiate_at a v d))) ",
                "(list_append (kapp_args (instantiate_at f v d)) (ListType.cons KExpr (instantiate_at a v d) (ListType.nil KExpr))) ",
                "{meet} ",
                "(kapp_args_app (instantiate_at f v d) (instantiate_at a v d)) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                "(fun (L : ListType KExpr) => list_append L (ListType.cons KExpr (instantiate_at a v d) (ListType.nil KExpr))) ",
                "(kapp_args (instantiate_at f v d)) (list_map {fmap} (kapp_args f)) (ihf g)))) ",
                // M -> RHS  (symm of RHS -> M)
                "(Eq.symm (ListType KExpr) (list_map {fmap} (kapp_args (KExpr.app f a))) {meet} ",
                "(Eq.trans (ListType KExpr) ",
                "(list_map {fmap} (kapp_args (KExpr.app f a))) ",
                "(list_map {fmap} (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "{meet} ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_map {fmap} L) ",
                "(kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) ",
                "(kapp_args_app f a)) ",
                "(Eq.trans (ListType KExpr) ",
                "(list_map {fmap} (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "(list_append (list_map {fmap} (kapp_args f)) (list_map {fmap} (ListType.cons KExpr a (ListType.nil KExpr)))) ",
                "{meet} ",
                "(list_map_append {fmap} (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) ",
                "(Eq.cong (ListType KExpr) (ListType KExpr) ",
                "(fun (L : ListType KExpr) => list_append (list_map {fmap} (kapp_args f)) L) ",
                "(list_map {fmap} (ListType.cons KExpr a (ListType.nil KExpr))) ",
                "(ListType.cons KExpr (instantiate_at a v d) (ListType.nil KExpr)) ",
                "(list_map_cons {fmap} a (ListType.nil KExpr)))))))"
            ),
            g_f = guard("f"),
            goal_f = goal_args("f"),
            g_a = guard("a"),
            goal_a = goal_args("a"),
            g_appfa = guard("(KExpr.app f a)"),
            fmap = fmap,
            meet = meet,
        );
        let kapp_args_value = format!(
            concat!(
                "fun (v : KExpr) (d : Nat) (nm : Name) (e : KExpr) => ",
                "KExpr.rec ",
                "(fun (e0 : KExpr) => {g_e0} -> {goal_e0}) ",
                "(fun (n : Level) {disch_sort}) ",
                "(fun (i : Nat) {disch_bvar}) ",
                "{app_arm} ",
                "(fun (ty : KExpr) (b : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihb : {g_b} -> {goal_b}) {disch_lam}) ",
                "(fun (ty : KExpr) (b : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihb : {g_b} -> {goal_b}) {disch_pi}) ",
                "(fun (nm0 : Name) (us : ListType Level) (g : {g_const}) => ",
                "Eq.refl (ListType KExpr) (ListType.nil KExpr)) ",
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihval : {g_val} -> {goal_val}) (_ihbody : {g_body} -> {goal_body}) {disch_let}) ",
                "(fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : {g_sub} -> {goal_sub}) {disch_proj}) ",
                "(fun (m : Nat) {disch_lit}) ",
                "e"
            ),
            g_e0 = guard("e0"),
            goal_e0 = goal_args("e0"),
            disch_sort = discharge_args("(KExpr.sort n)"),
            disch_bvar = discharge_args("(KExpr.bvar i)"),
            app_arm = app_arm,
            g_ty = guard("ty"),
            goal_ty = goal_args("ty"),
            g_b = guard("b"),
            goal_b = goal_args("b"),
            disch_lam = discharge_args("(KExpr.lam ty b)"),
            disch_pi = discharge_args("(KExpr.pi ty b)"),
            g_const = guard("(KExpr.const nm0 us)"),
            g_val = guard("val"),
            goal_val = goal_args("val"),
            g_body = guard("body"),
            goal_body = goal_args("body"),
            disch_let = discharge_args("(KExpr.let_ ty val body)"),
            g_sub = guard("sub"),
            goal_sub = goal_args("sub"),
            disch_proj = discharge_args("(KExpr.proj s i sub)"),
            disch_lit = discharge_args("(KExpr.lit m)"),
        );

        self.add_definition(SpecDefinition {
            name: "instantiate_at_kapp_args_const".to_string(),
            type_src: format!(
                "forall (v : KExpr) (d : Nat) (nm : Name) (e : KExpr), {g} -> {goal}",
                g = guard("e"),
                goal = goal_args("e"),
            ),
            value_src: Some(kapp_args_value),
            is_axiom: false,
            description: concat!(
                "Under the head-const guard, kapp_args commutes with instantiate_at up to list_map: ",
                "kapp_args (instantiate_at e v d) = list_map (instantiate_at . v d) (kapp_args e). KExpr.rec ",
                "on e — const arm genuine (both sides reduce to nil), app arm a chain (kapp_args_app + ",
                "instantiate_at_app + IH + list_map_append), sort/bvar/lam/pi discharged by the guard. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment E)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kapp_args".to_string(),
                "kapp_fn".to_string(),
                "kexpr_const_name".to_string(),
                "instantiate_at".to_string(),
                "instantiate_at_app".to_string(),
                "kapp_args_app".to_string(),
                "list_map".to_string(),
                "list_map_append".to_string(),
                "list_map_cons".to_string(),
                "KExpr.rec".to_string(),
                "opt_is_none".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kexpr_const_name_inst_some: if kexpr_const_name h = some nm then
        // instantiate_at fixes the head name. KExpr.rec on h — const arm genuine
        // (instantiate_at_const), ALL other arms (incl app) discharged (their
        // kexpr_const_name is none, so the guard none = some is absurd).
        let guard_h = |h: &str| {
            format!("Eq (OptionType Name) (kexpr_const_name {h}) (OptionType.some Name nm)")
        };
        let goal_h = |h: &str| {
            format!(
                "Eq (OptionType Name) (kexpr_const_name (instantiate_at {h} v d)) (kexpr_const_name {h})"
            )
        };
        let disch_h = |ctor: &str| {
            format!(
                "(g : {g}) => Empty.rec (fun (_ : Empty) => {goal}) \
                 (Eq.substType (OptionType Name) (opt_is_none Name) \
                 (OptionType.none Name) (OptionType.some Name nm) g Nat.zero)",
                g = guard_h(ctor),
                goal = goal_h(ctor),
            )
        };
        let inst_some_value = format!(
            concat!(
                "fun (v : KExpr) (d : Nat) (nm : Name) (h : KExpr) => ",
                "KExpr.rec ",
                "(fun (h0 : KExpr) => {g_h0} -> {goal_h0}) ",
                "(fun (n : Level) {disch_sort}) ",
                "(fun (i : Nat) {disch_bvar}) ",
                "(fun (f : KExpr) (a : KExpr) (_ihf : {g_f} -> {goal_f}) (_iha : {g_a} -> {goal_a}) {disch_app}) ",
                "(fun (ty : KExpr) (b : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihb : {g_b} -> {goal_b}) {disch_lam}) ",
                "(fun (ty : KExpr) (b : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihb : {g_b} -> {goal_b}) {disch_pi}) ",
                "(fun (nm0 : Name) (us : ListType Level) (g : {g_const}) => ",
                "Eq.cong KExpr (OptionType Name) (fun (X : KExpr) => kexpr_const_name X) ",
                "(instantiate_at (KExpr.const nm0 us) v d) (KExpr.const nm0 us) ",
                "(instantiate_at_const nm0 us v d)) ",
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (_ihty : {g_ty} -> {goal_ty}) (_ihval : {g_val} -> {goal_val}) (_ihbody : {g_body} -> {goal_body}) {disch_let}) ",
                "(fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : {g_sub} -> {goal_sub}) {disch_proj}) ",
                "(fun (m : Nat) {disch_lit}) ",
                "h"
            ),
            g_h0 = guard_h("h0"),
            goal_h0 = goal_h("h0"),
            disch_sort = disch_h("(KExpr.sort n)"),
            disch_bvar = disch_h("(KExpr.bvar i)"),
            g_f = guard_h("f"),
            goal_f = goal_h("f"),
            g_a = guard_h("a"),
            goal_a = goal_h("a"),
            disch_app = disch_h("(KExpr.app f a)"),
            g_ty = guard_h("ty"),
            goal_ty = goal_h("ty"),
            g_b = guard_h("b"),
            goal_b = goal_h("b"),
            disch_lam = disch_h("(KExpr.lam ty b)"),
            disch_pi = disch_h("(KExpr.pi ty b)"),
            g_const = guard_h("(KExpr.const nm0 us)"),
            g_val = guard_h("val"),
            goal_val = goal_h("val"),
            g_body = guard_h("body"),
            goal_body = goal_h("body"),
            disch_let = disch_h("(KExpr.let_ ty val body)"),
            g_sub = guard_h("sub"),
            goal_sub = goal_h("sub"),
            disch_proj = disch_h("(KExpr.proj s i sub)"),
            disch_lit = disch_h("(KExpr.lit m)"),
        );
        self.add_definition(SpecDefinition {
            name: "kexpr_const_name_inst_some".to_string(),
            type_src: format!(
                "forall (v : KExpr) (d : Nat) (nm : Name) (h : KExpr), {g} -> {goal}",
                g = guard_h("h"),
                goal = goal_h("h"),
            ),
            value_src: Some(inst_some_value),
            is_axiom: false,
            description: "If kexpr_const_name h = some nm, then kexpr_const_name (instantiate_at h v d) = kexpr_const_name h (a const head is fixed by instantiate_at). KExpr.rec on h, const arm via instantiate_at_const, others guard-discharged. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kexpr_const_name".to_string(),
                "instantiate_at".to_string(),
                "instantiate_at_const".to_string(),
                "KExpr.rec".to_string(),
                "opt_is_none".to_string(),
                "Eq.substType".to_string(),
                "Empty.rec".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kexpr_const_name_instantiate_const: under the head-const guard, the
        // recovered const name survives instantiate_at — so iota_reduct(inst e)
        // looks up the SAME recursor/constructor. Composes instantiate_at_kapp_fn_const
        // (kapp_fn commutes) and kexpr_const_name_inst_some (const name fixed).
        self.add_definition(SpecDefinition {
            name: "kexpr_const_name_instantiate_const".to_string(),
            type_src: format!(
                "forall (v : KExpr) (d : Nat) (nm : Name) (e : KExpr), {g} -> \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn (instantiate_at e v d))) (kexpr_const_name (kapp_fn e))",
                g = guard("e"),
            ),
            value_src: Some(format!(
                concat!(
                    "fun (v : KExpr) (d : Nat) (nm : Name) (e : KExpr) (g : {g}) => ",
                    "Eq.trans (OptionType Name) ",
                    "(kexpr_const_name (kapp_fn (instantiate_at e v d))) ",
                    "(kexpr_const_name (instantiate_at (kapp_fn e) v d)) ",
                    "(kexpr_const_name (kapp_fn e)) ",
                    "(Eq.cong KExpr (OptionType Name) (fun (X : KExpr) => kexpr_const_name X) ",
                    "(kapp_fn (instantiate_at e v d)) (instantiate_at (kapp_fn e) v d) ",
                    "(instantiate_at_kapp_fn_const v d nm e g)) ",
                    "(kexpr_const_name_inst_some v d nm (kapp_fn e) g)"
                ),
                g = guard("e"),
            )),
            is_axiom: false,
            description: "Under the head-const guard, kexpr_const_name (kapp_fn (instantiate_at e v d)) = kexpr_const_name (kapp_fn e): the recovered recursor/constructor name survives instantiate_at, so iota_reduct(inst e) looks up the same rule. Composes instantiate_at_kapp_fn_const + kexpr_const_name_inst_some. DerivedProved, zero axiom_deps. Part of #2859 (Increment E).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "instantiate_at".to_string(),
                "instantiate_at_kapp_fn_const".to_string(),
                "kexpr_const_name_inst_some".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
