// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typing predicates and definitional equality (PARTs 5, DefEq, Delta/Iota)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_typing_def_eq(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 5: Type Checking Predicates
        // =========================================================
        //
        // Typing is defined as an inductive type family to enable structural
        // induction on typing derivations. This is required for proving
        // substitution_typing and other metatheoretic properties constructively.
        //
        // Reference: MetaCoq (JAR 2020), Lean4Lean - standard approach for
        // verified type theory formalizations.
        //
        // Part of #351: substitution_typing needs inductive has_type
        //
        // Typing is now a GENUINE `add_inductive` (formerly the type + the five
        // constructors sort/pi/lam/app/conv + the recursor were 7 separate
        // FoundationalRule axioms, split across this function and
        // add_typing_conv_and_rec because Typing.conv references DefEq). It is
        // registered AFTER the DefEq inductive below, because the `conv`
        // constructor's field type references `DefEq A B` (DefEq must already be
        // in the env when Typing is elaborated). Every constructor type transcribes
        // its retired axiom BYTE-IDENTICALLY, and the kernel GENERATES `Typing.rec`
        // (positivity-checked, sound by construction). See the add_inductive call
        // after the DefEq block. Part of the inductive-encoding drain (POC: DefEq).

        // =========================================================
        // DefEq: Inductive definitional equality (Part of #359)
        // =========================================================
        // DefEq is the inductive type for definitional equality judgments.
        // This enables structural induction on equality proofs for TypePreservation.
        // See: designs/2026-01-30-inductive-def-eq.md
        //
        // DefEq was previously a HAND-AXIOMATIZED inductive: the type, all nine
        // constructors (refl/symm/trans/beta/app_cong/lam_cong/pi_cong/delta/iota)
        // AND the recursor were 11 separate FoundationalRule axioms (is_axiom:true,
        // value-less), split across this function and
        // add_typing_def_eq_delta_iota_rec because delta/iota reference
        // delta_reduces/iota_reduces (defined in the reduction_families stage).
        // It is now a GENUINE inductive registered via `add_inductive` — the same
        // retirement applied to iota_reduces / delta_reduces / KernelAddDeclChain /
        // KernelInferAccepts. Every constructor type transcribes its retired axiom
        // BYTE-IDENTICALLY (no strengthening/weakening — DefEq is exactly the
        // standard equivalence-and-congruence closure with the β/δ/ι base rules),
        // and the kernel GENERATES `DefEq.rec` (positivity-checked, sound by
        // construction). All 11 names now lower to non-Axiom kernel declarations
        // (Inductive / Constructor / Recursor) and leave the ConstantKind::Axiom
        // census (62 -> 51). Because DefEq's two arguments are NON-UNIFORM across
        // constructors (refl -> a a, symm concludes DefEq b a, beta -> app/instantiate,
        // ...), fixedIndicesToParams does NOT promote them: they stay genuine
        // INDICES, so the generated recursor keeps the 3-ary index motive
        // (`fun (a b : KExpr) (h : DefEq a b) => ...`) and the minor-premise ORDER
        // matches the retired hand-written DefEq.rec — every downstream DefEq.rec
        // consumer (def_eq_respects_lift_at, def_eq_joinable, def_eq_respects_subst_at)
        // elaborates against the generated recursor unchanged. The reduction_families
        // stage now runs BEFORE this one (see bundles.rs) so delta_reduces/iota_reduces
        // exist for the delta/iota fields. ZERO new axioms. Part of the DefEq
        // inductive-encoding drain (POC for Typing/TypedDefEq/DefinitionalExtension/
        // ProdType).
        self.add_inductive(
            concat!(
                "inductive DefEq : KExpr -> KExpr -> Type\n",
                "| refl : forall (a : KExpr), DefEq a a\n",
                "| symm : forall (a : KExpr) (b : KExpr), DefEq a b -> DefEq b a\n",
                "| trans : forall (a : KExpr) (b : KExpr) (c : KExpr), DefEq a b -> DefEq b c -> DefEq a c\n",
                "| beta : forall (A : KExpr) (b : KExpr) (a : KExpr), DefEq (KExpr.app (KExpr.lam A b) a) (instantiate b a)\n",
                "| app_cong : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), DefEq f f' -> DefEq a a' -> DefEq (KExpr.app f a) (KExpr.app f' a')\n",
                "| lam_cong : forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr), DefEq A A' -> DefEq b b' -> DefEq (KExpr.lam A b) (KExpr.lam A' b')\n",
                "| pi_cong : forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr), DefEq A A' -> DefEq B B' -> DefEq (KExpr.pi A B) (KExpr.pi A' B')\n",
                "| delta : forall (e : KExpr) (e' : KExpr), delta_reduces e e' -> DefEq e e'\n",
                "| iota : forall (e : KExpr) (e' : KExpr), iota_reduces e e' -> DefEq e e'\n",
                "| zeta : forall (ty : KExpr) (v : KExpr) (b : KExpr), DefEq (KExpr.let_ ty v b) (instantiate b v)\n",
                "| let_cong : forall (ty : KExpr) (ty' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr), DefEq ty ty' -> DefEq v v' -> DefEq b b' -> DefEq (KExpr.let_ ty v b) (KExpr.let_ ty' v' b')\n",
                "| proj_cong : forall (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr), DefEq sub sub' -> DefEq (KExpr.proj s i sub) (KExpr.proj s i sub')"
            ),
            "Inductive definitional equality: DefEq a b means a ≡ b. Faithful nine-constructor inductive (formerly 11 hand axioms: the type, refl/symm/trans/beta/app_cong/lam_cong/pi_cong/delta/iota, and a hand-written recursor). refl/symm/trans give the equivalence closure; app_cong/lam_cong/pi_cong the congruence closure; beta the literal UNTYPED kernel β rule ((λA.b) a ≡ b[a/0], no typing premises — church_rosser_whnf retirement track); delta/iota carry a genuine directed delta_reduces / iota_reduces step over the fixed the_red_env. Every constructor type is byte-identical to its retired axiom; the kernel generates DefEq.rec, sound by construction. ZERO new axioms.",
        )?;

        // =========================================================
        // Typing: inductive typing judgment (registered AFTER DefEq — conv needs it)
        // =========================================================
        //
        // Typing was previously a HAND-AXIOMATIZED inductive: the type, the five
        // constructors (sort/pi/lam/app/conv) AND the recursor were 7 separate
        // FoundationalRule axioms (is_axiom:true, value-less), split across
        // add_typing_def_eq (type + sort/pi/lam/app) and add_typing_conv_and_rec
        // (conv + rec) because Typing.conv references DefEq. It is now a GENUINE
        // inductive registered via `add_inductive` — the same retirement applied
        // to DefEq / ConstantExtension / InductiveExtension. Every constructor type
        // transcribes its retired axiom BYTE-IDENTICALLY (no strengthening/
        // weakening), and the kernel GENERATES `Typing.rec` (positivity-checked,
        // sound by construction). All 7 names now lower to non-Axiom kernel
        // declarations (Inductive / Constructor / Recursor) and leave the
        // ConstantKind::Axiom census. Because Typing's two arguments (e, T) are
        // NON-UNIFORM across constructors (sort -> sort n / sort (succ n), conv
        // concludes Typing e B, ...), fixedIndicesToParams does NOT promote them:
        // they stay genuine INDICES, so the generated recursor keeps the 2-ary
        // index motive (`fun (e T : KExpr) (h : Typing e T) => ...`) and the
        // minor-premise ORDER matches the retired hand-written Typing.rec — every
        // downstream Typing.rec consumer elaborates against the generated recursor
        // unchanged. The `conv` constructor carries the raw (untyped) `DefEq A B`
        // (church_rosser_whnf retirement track), byte-identical to the retired
        // Typing.conv axiom. add_typing_conv_and_rec is now a no-op. ZERO new
        // axioms.
        self.add_inductive(
            concat!(
                "inductive Typing : KExpr -> KExpr -> Type\n",
                "| sort : forall (n : Level), Typing (KExpr.sort n) (KExpr.sort (Level.succ n))\n",
                "| pi : forall (A : KExpr) (B : KExpr) (n : Level) (m : Level), Typing A (KExpr.sort n) -> Typing B (KExpr.sort m) -> Typing (KExpr.pi A B) (KExpr.sort (Level.imax n m))\n",
                "| lam : forall (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), Typing A (KExpr.sort u) -> Typing b B -> Typing (KExpr.lam A b) (KExpr.pi A B)\n",
                "| app : forall (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), Typing f (KExpr.pi A B) -> Typing a A -> Typing (KExpr.app f a) (instantiate B a)\n",
                "| conv : forall (e : KExpr) (A : KExpr) (B : KExpr), Typing e A -> DefEq A B -> Typing e B"
            ),
            "Inductive typing judgment: Typing e T means expression e has type T. Faithful five-constructor inductive (formerly 7 hand axioms: the type, sort/pi/lam/app/conv, and a hand-written recursor). sort/pi/lam/app are the standard CIC formation and introduction rules (pi/lam universe-aware, #2870; app dependent, #464); conv is the literal CIC conversion rule carrying the raw UNTYPED DefEq A B (church_rosser_whnf retirement track). Every constructor type is byte-identical to its retired axiom; the kernel generates Typing.rec, sound by construction. Registered after the DefEq inductive because conv references DefEq. ZERO new axioms.",
        )?;

        // Transport DefEq along Eq: if a = a' and DefEq a' b, then DefEq a b.
        // Required for deriving beta_subst_commutes from instantiate_at_zero_commutes (#661).
        // Proof: Eq.substType KExpr (fun x => DefEq x b) a' a (Eq.symm KExpr a a' eq) h
        self.add_definition(SpecDefinition {
            name: "def_eq_eq_left".to_string(),
            type_src: "forall (a : KExpr) (a' : KExpr) (b : KExpr), Eq KExpr a a' -> DefEq a' b -> DefEq a b".to_string(),
            value_src: Some(
                "fun (a : KExpr) (a' : KExpr) (b : KExpr) (eq : Eq KExpr a a') (h : DefEq a' b) => Eq.substType KExpr (fun (x : KExpr) => DefEq x b) a' a (Eq.symm KExpr a a' eq) h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Transport DefEq left: Eq a a' -> DefEq a' b -> DefEq a b. DerivedProved: all deps (Eq.subst, Eq.symm) are FoundationalRules. Part of #661, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Transport DefEq along Eq on right: if DefEq a b' and b' = b, then DefEq a b.
        // Proof: Eq.substType KExpr (fun x => DefEq a x) b' b eq h
        self.add_definition(SpecDefinition {
            name: "def_eq_eq_right".to_string(),
            type_src: "forall (a : KExpr) (b' : KExpr) (b : KExpr), DefEq a b' -> Eq KExpr b' b -> DefEq a b".to_string(),
            value_src: Some(
                "fun (a : KExpr) (b' : KExpr) (b : KExpr) (h : DefEq a b') (eq : Eq KExpr b' b) => Eq.substType KExpr (fun (x : KExpr) => DefEq a x) b' b eq h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Transport DefEq right: DefEq a b' -> Eq b' b -> DefEq a b. DerivedProved: Eq.substType is FoundationalRule. Part of #661, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.substType".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // is_def_eq: Type alias for backward compatibility
        // Previously an axiom, now defined as DefEq.
        // Registered as reducible Definition (not Opaque) so the kernel can
        // unfold is_def_eq ↔ DefEq during definitional equality checking.
        // This is a one-step alias, so the "expensive reduction" concern from
        // #1385 does not apply. Part of #464: resolve Opaque alias barrier.
        self.add_definition_reducible(SpecDefinition {
            name: "is_def_eq".to_string(),
            type_src: "KExpr -> KExpr -> Type".to_string(),
            value_src: Some("fun (a : KExpr) (b : KExpr) => DefEq a b".to_string()),
            is_axiom: false,
            description: "Definitional equality (alias): is_def_eq a b := DefEq a b. Reducible for Opaque barrier bypass.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // has_type: Type alias for backward compatibility
        // Previously an axiom, now defined as Typing.
        // Registered as reducible Definition (not Opaque) so the kernel can
        // unfold has_type ↔ Typing during definitional equality checking.
        // Part of #464: resolve Opaque alias barrier (same as is_def_eq above).
        self.add_definition_reducible(SpecDefinition {
            name: "has_type".to_string(),
            type_src: "KExpr -> KExpr -> Type".to_string(),
            value_src: Some("fun (e : KExpr) (T : KExpr) => Typing e T".to_string()),
            is_axiom: false,
            description: "Typing judgment (alias): has_type e T := Typing e T. Reducible for Opaque barrier bypass.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // NOTE: Typing (type + sort/pi/lam/app/conv) and its generated recursor
        // Typing.rec are all provided by the single `add_inductive Typing` above.
        // add_typing_conv_and_rec is now a documented no-op.

        // Pi injectivity at DefEq level is in pi_injectivity_def_eq.rs (Part of #464)

        Ok(())
    }

    /// Formerly registered `Typing.conv` and `Typing.rec` as two separate
    /// hand-written FoundationalRule axioms (split out of `add_typing_def_eq` so
    /// that `Typing.conv` could reference `DefEq`, which was originally registered
    /// mid-`add_typing_def_eq`). Both are now provided by the single
    /// `add_inductive Typing` in `add_typing_def_eq` — which is registered AFTER
    /// the DefEq inductive there, so the `conv` constructor's `DefEq A B` field
    /// resolves. `Typing.conv` is a genuine constructor and `Typing.rec` is the
    /// kernel-generated recursor. This function is retained (still called from
    /// `add_typing_def_eq_typed_support`) as a documented no-op to avoid churning
    /// the call sites.
    ///
    /// The retired hand-written `Typing.rec` had type shape (verbatim, for
    /// faithfulness comparison against the generated recursor):
    /// ```text
    /// forall (P : forall (e T : KExpr), Typing e T -> Type),
    ///   (forall n, P (sort n) (sort (succ n)) (Typing.sort n)) ->                    -- sort
    ///   (forall A B n m (hA : Typing A (sort n)) (hB : Typing B (sort m)),
    ///      P A (sort n) hA -> P B (sort m) hB ->
    ///      P (pi A B) (sort (imax_nat n m)) (Typing.pi A B n m hA hB)) ->            -- pi
    ///   (forall A b B u (hA : Typing A (sort u)) (hb : Typing b B),
    ///      P A (sort u) hA -> P b B hb ->
    ///      P (lam A b) (pi A B) (Typing.lam A b B u hA hb)) ->                       -- lam
    ///   (forall f a A B (hf : Typing f (pi A B)) (ha : Typing a A),
    ///      P f (pi A B) hf -> P a A ha ->
    ///      P (app f a) (instantiate B a) (Typing.app f a A B hf ha)) ->             -- app
    ///   (forall e A B (he : Typing e A) (eq : DefEq A B),
    ///      P e A he -> P e B (Typing.conv e A B he eq)) ->                          -- conv
    ///   forall (e T : KExpr) (h : Typing e T), P e T h
    /// ```
    /// Because Typing is a 0-parameter / 2-index family, the kernel recursor layout
    /// `motive -> minors -> indices -> major` reproduces exactly this argument
    /// order, so every downstream `Typing.rec` consumer is unchanged.
    pub(super) fn add_typing_conv_and_rec(&mut self) -> Result<(), SpecError> {
        // No-op: Typing.conv is a constructor and Typing.rec is the generated
        // recursor of the `add_inductive Typing` in add_typing_def_eq.
        Ok(())
    }

    /// Formerly registered `DefEq.delta`, `DefEq.iota`, and `DefEq.rec` as three
    /// separate hand-written FoundationalRule axioms (split out of
    /// `add_typing_def_eq` so they could reference `delta_reduces` / `iota_reduces`
    /// from the reduction-families stage). All three are now provided by the single
    /// `add_inductive DefEq` in `add_typing_def_eq` (the `reduction_families` stage
    /// runs BEFORE it, so the δ/ι constructor fields resolve): `DefEq.delta` /
    /// `DefEq.iota` are genuine constructors and `DefEq.rec` is the kernel-generated
    /// recursor. This stage is now a documented no-op, retained as a bundle stage to
    /// avoid churning the STAGES table (removing it would renumber the plan).
    ///
    /// The retired hand-written `DefEq.rec` had type shape (verbatim, for
    /// reference / faithfulness comparison against the generated recursor):
    /// ```text
    /// forall (P : forall (a b : KExpr), DefEq a b -> Type),
    ///   (forall a, P a a (DefEq.refl a)) ->                       -- refl
    ///   (forall a b (h : DefEq a b), P a b h -> P b a (DefEq.symm a b h)) -> -- symm
    ///   (forall a b c (hab : DefEq a b) (hbc : DefEq b c),
    ///      P a b hab -> P b c hbc -> P a c (DefEq.trans a b c hab hbc)) ->   -- trans
    ///   (forall A body arg,
    ///      P (app (lam A body) arg) (instantiate body arg) (DefEq.beta A body arg)) -> -- beta
    ///   (forall f f' a a' (hf : DefEq f f') (ha : DefEq a a'),
    ///      P f f' hf -> P a a' ha -> P (app f a) (app f' a') (DefEq.app_cong ...)) -> -- app_cong
    ///   (forall A A' b b' ... P (lam A b) (lam A' b') (DefEq.lam_cong ...)) ->        -- lam_cong
    ///   (forall A A' B B' ... P (pi A B) (pi A' B') (DefEq.pi_cong ...)) ->           -- pi_cong
    ///   (forall e e' (hd : delta_reduces e e'), P e e' (DefEq.delta e e' hd)) ->      -- delta
    ///   (forall e e' (hi : iota_reduces e e'), P e e' (DefEq.iota e e' hi)) ->        -- iota
    ///   forall (a b : KExpr) (h : DefEq a b), P a b h
    /// ```
    /// Because DefEq is a 0-parameter / 2-index family, the kernel recursor layout
    /// `motive -> minors -> indices -> major` reproduces exactly this argument
    /// order, so every downstream `DefEq.rec` consumer is unchanged.
    pub(super) fn add_typing_def_eq_delta_iota_rec(&mut self) -> Result<(), SpecError> {
        // No-op: DefEq.delta / DefEq.iota are constructors and DefEq.rec is the
        // generated recursor of the `add_inductive DefEq` in add_typing_def_eq.
        Ok(())
    }
}
#[cfg(test)]
#[path = "typing_def_eq_tests.rs"]
mod typing_def_eq_tests;
