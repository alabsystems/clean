// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-parameter support over the existing Level, level lists, and KExpr.
//!
//! Membership is an equality about the actual first-match nameIdx operation.
//! These predicates are available before declaration signatures and typing;
//! they do not assert that production admission has established support.
//! Neither parameter uniqueness nor argument arity is part of support.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Requires only foundation/expr/rec_env and univ_instantiation_syntax.
    pub(super) fn add_universe_param_support(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive LevelParamSupport (ps : ListType Name) : Level -> Prop
| zero : LevelParamSupport ps Level.zero
| succ : forall (u : Level), LevelParamSupport ps u -> LevelParamSupport ps (Level.succ u)
| max : forall (u : Level) (v : Level), LevelParamSupport ps u -> LevelParamSupport ps v -> LevelParamSupport ps (Level.max u v)
| imax : forall (u : Level) (v : Level), LevelParamSupport ps u -> LevelParamSupport ps v -> LevelParamSupport ps (Level.imax u v)
| param : forall (n : Name) (i : Nat), Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) -> LevelParamSupport ps (Level.param n)",
            "Every universe parameter of a raw Level has an actual first-match index in the declared parameter list. No arity or uniqueness assumption is added.",
        )?;
        self.add_inductive(
            r"inductive LevelListParamSupport (ps : ListType Name) : ListType Level -> Prop
| nil : LevelListParamSupport ps (ListType.nil Level)
| cons : forall (u : Level) (us : ListType Level), LevelParamSupport ps u -> LevelListParamSupport ps us -> LevelListParamSupport ps (ListType.cons Level u us)",
            "Parameter support traverses every level in a constant's level argument list, including nested max/imax/succ structure.",
        )?;
        self.add_inductive(
            r"inductive KExprParamSupport (ps : ListType Name) : KExpr -> Prop
| sort : forall (u : Level), LevelParamSupport ps u -> KExprParamSupport ps (KExpr.sort u)
| bvar : forall (i : Nat), KExprParamSupport ps (KExpr.bvar i)
| app : forall (f : KExpr) (a : KExpr), KExprParamSupport ps f -> KExprParamSupport ps a -> KExprParamSupport ps (KExpr.app f a)
| lam : forall (A : KExpr) (b : KExpr), KExprParamSupport ps A -> KExprParamSupport ps b -> KExprParamSupport ps (KExpr.lam A b)
| pi : forall (A : KExpr) (B : KExpr), KExprParamSupport ps A -> KExprParamSupport ps B -> KExprParamSupport ps (KExpr.pi A B)
| const : forall (n : Name) (us : ListType Level), LevelListParamSupport ps us -> KExprParamSupport ps (KExpr.const n us)
| let_ : forall (A : KExpr) (v : KExpr) (b : KExpr), KExprParamSupport ps A -> KExprParamSupport ps v -> KExprParamSupport ps b -> KExprParamSupport ps (KExpr.let_ A v b)
| proj : forall (sn : Name) (i : Nat) (sub : KExpr), KExprParamSupport ps sub -> KExprParamSupport ps (KExpr.proj sn i sub)
| lit : forall (n : Nat), KExprParamSupport ps (KExpr.lit n)",
            "Universe support over all nine existing KExpr constructors. Term binders do not shift universe names; projection children and every constant level are traversed, and every tagged literal payload is preserved. This is not de Bruijn closedness or a typing judgment.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;

    #[test]
    fn support_predicates_register_early_and_cover_all_expression_constructors() {
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
                .expect("raw universe syntax");
            spec.add_universe_param_support()
                .expect("early support predicates");
            for later in [
                "DefEnv",
                "KDefSig",
                "evalL",
                "TypingCtx",
                "universe_bridge_congr2",
            ] {
                assert!(
                    !spec.definitions().contains_key(later),
                    "support must not depend on {later}"
                );
            }
            let ps = "(ListType.nil Name)";
            let z = "(KExpr.sort Level.zero)";
            let hz =
                format!("(KExprParamSupport.sort {ps} Level.zero (LevelParamSupport.zero {ps}))");
            for (suffix, expression, proof) in [
                ("sort", z.to_string(), hz.clone()),
                ("bvar", "(KExpr.bvar Nat.zero)".to_string(), format!("KExprParamSupport.bvar {ps} Nat.zero")),
                ("app", format!("(KExpr.app {z} {z})"), format!("KExprParamSupport.app {ps} {z} {z} {hz} {hz}")),
                ("lam", format!("(KExpr.lam {z} {z})"), format!("KExprParamSupport.lam {ps} {z} {z} {hz} {hz}")),
                ("pi", format!("(KExpr.pi {z} {z})"), format!("KExprParamSupport.pi {ps} {z} {z} {hz} {hz}")),
                ("const", "(KExpr.const Name.anonymous (ListType.nil Level))".to_string(), format!("KExprParamSupport.const {ps} Name.anonymous (ListType.nil Level) (LevelListParamSupport.nil {ps})")),
                ("let", format!("(KExpr.let_ {z} {z} {z})"), format!("KExprParamSupport.let_ {ps} {z} {z} {z} {hz} {hz} {hz}")),
                ("proj", format!("(KExpr.proj Name.anonymous Nat.zero {z})"), format!("KExprParamSupport.proj {ps} Name.anonymous Nat.zero {z} {hz}")),
                ("lit", "(KExpr.lit (Nat.succ Nat.zero))".to_string(), format!("KExprParamSupport.lit {ps} (Nat.succ Nat.zero)")),
            ] {
                let name = format!("support_early_{suffix}_witness");
                spec.add_recursive_def(
                    &format!("def {name} : KExprParamSupport {ps} {expression} := {proof}"),
                    "Checked early support constructor witness; no typing claim.",
                ).expect("all expression support constructors must check");
                assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, &name).is_empty());
            }
            assert!(spec.add_recursive_def(
                "def support_missing_member_must_fail : LevelParamSupport (ListType.nil Name) (Level.param Name.anonymous) := LevelParamSupport.param (ListType.nil Name) Name.anonymous Nat.zero (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero))",
                "Negative control: unknown parameters do not acquire a fabricated membership witness.",
            ).is_err());
        });
    }
}
