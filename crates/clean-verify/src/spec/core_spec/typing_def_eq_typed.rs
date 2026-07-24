// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typed definitional equality lane for the conversion surface.
//!
//! `TypedDefEq` is a separate equality relation carrying typed beta premises.
//! It exists to close the `DefEq.rec_beta_typed` gap (#2872): the raw `DefEq`
//! inductive has an untyped beta constructor, but `Typing.conv` and the #464
//! type-preservation chain need typed beta evidence.
//!
//! Architecture:
//! - Raw lane: `DefEq` (unchanged, used by kernel-model and micro-checker)
//! - Typed lane: `TypedDefEq` (this module, used by Typing.conv and type preservation)
//! - One-way bridge: `typed_def_eq_to_def_eq : TypedDefEq e e' -> DefEq e e'`
//! - Alias: `typing_is_def_eq := TypedDefEq`
//!
//! Part of #2872, #464.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register `TypedDefEq`, its constructors, recursor, one-way bridge, the
    /// `typing_is_def_eq` alias, and then the `Typing.conv` / `Typing.rec`
    /// surfaces that consume that alias.
    ///
    /// MUST be called AFTER `add_typing_def_eq_delta_iota_rec()` because
    /// `TypedDefEq.delta` references `delta_reduces` and `TypedDefEq.iota`
    /// references `iota_reduces`. The bridge `typed_def_eq_to_def_eq` also
    /// references raw `DefEq` constructors.
    ///
    /// Part of #2872.
    pub(super) fn add_typing_def_eq_typed_support(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // TypedDefEq: Typed definitional equality (Part of #2872)
        // =========================================================
        //
        // TypedDefEq was previously a HAND-AXIOMATIZED inductive: the type, all
        // nine constructors (refl/symm/trans/beta/app_cong/lam_cong/pi_cong/delta/
        // iota) AND the recursor were 11 separate FoundationalRule axioms
        // (is_axiom:true, value-less). It is now a GENUINE inductive registered via
        // `add_inductive` — the same retirement applied to DefEq / Typing. Every
        // constructor type transcribes its retired axiom BYTE-IDENTICALLY (no
        // strengthening/weakening — TypedDefEq is the typed-beta twin of DefEq: the
        // same equivalence-and-congruence closure, but with the beta constructor
        // carrying the codomain B, domain universe u, and the three Typing premises
        // (hA/hbody/harg) that the conversion/preservation lanes need). The kernel
        // GENERATES `TypedDefEq.rec` (positivity-checked, sound by construction).
        // All 11 names now lower to non-Axiom kernel declarations (Inductive /
        // Constructor / Recursor) and leave the ConstantKind::Axiom census. Because
        // TypedDefEq's two arguments are NON-UNIFORM across constructors (refl ->
        // a a, symm concludes TypedDefEq b a, beta -> app/instantiate, ...),
        // fixedIndicesToParams does NOT promote them: they stay genuine INDICES, so
        // the generated recursor keeps the 2-ary index motive
        // (`fun (a b : KExpr) (h : TypedDefEq a b) => ...`) and the minor-premise
        // ORDER matches the retired hand-written TypedDefEq.rec — the sole
        // downstream consumer, the DerivedProved `typed_def_eq_to_def_eq` bridge
        // below, elaborates against the generated recursor unchanged. The beta minor
        // exposes B, u, hA, hbody, harg exactly as before. TypedDefEq.beta
        // references Typing (now a genuine inductive) and delta/iota reference
        // delta_reduces / iota_reduces (all already in the env at this stage). ZERO
        // new axioms. Part of the inductive-encoding drain (after DefEq / Typing).
        self.add_inductive(
            concat!(
                "inductive TypedDefEq : KExpr -> KExpr -> Type\n",
                "| refl : forall (a : KExpr), TypedDefEq a a\n",
                "| symm : forall (a : KExpr) (b : KExpr), TypedDefEq a b -> TypedDefEq b a\n",
                "| trans : forall (a : KExpr) (b : KExpr) (c : KExpr), TypedDefEq a b -> TypedDefEq b c -> TypedDefEq a c\n",
                "| beta : forall (A : KExpr) (body : KExpr) (arg : KExpr) (B : KExpr) (u : Level), Typing A (KExpr.sort u) -> Typing body B -> Typing arg A -> TypedDefEq (KExpr.app (KExpr.lam A body) arg) (instantiate body arg)\n",
                "| app_cong : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), TypedDefEq f f' -> TypedDefEq a a' -> TypedDefEq (KExpr.app f a) (KExpr.app f' a')\n",
                "| lam_cong : forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr), TypedDefEq A A' -> TypedDefEq b b' -> TypedDefEq (KExpr.lam A b) (KExpr.lam A' b')\n",
                "| pi_cong : forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr), TypedDefEq A A' -> TypedDefEq B B' -> TypedDefEq (KExpr.pi A B) (KExpr.pi A' B')\n",
                "| delta : forall (e : KExpr) (e' : KExpr), delta_reduces e e' -> TypedDefEq e e'\n",
                "| iota : forall (e : KExpr) (e' : KExpr), iota_reduces e e' -> TypedDefEq e e'"
            ),
            "Typed definitional equality: TypedDefEq e e' carries typing premises on the beta constructor. Faithful nine-constructor inductive (formerly 11 hand axioms: the type, refl/symm/trans/beta/app_cong/lam_cong/pi_cong/delta/iota, and a hand-written recursor). refl/symm/trans give the equivalence closure; app_cong/lam_cong/pi_cong the congruence closure; beta is the TYPED beta rule ((λA.b) a ≡_t b[a/0]) carrying codomain B, domain universe u, and Typing premises for A/body/arg (#2870-compatible); delta/iota carry a directed delta_reduces / iota_reduces step. Used by the conversion surface (Typing.conv, type_conversion, TypePreservation) via the typing_is_def_eq alias. Every constructor type is byte-identical to its retired axiom; the kernel generates TypedDefEq.rec, sound by construction. ZERO new axioms. Part of #2872.",
        )?;

        // =========================================================
        // One-way bridge: TypedDefEq → DefEq
        // =========================================================

        // typed_def_eq_to_def_eq: every typed equality is a raw equality.
        // Proof by TypedDefEq.rec, mapping each constructor to its raw counterpart.
        // The beta case drops the typing premises and uses raw DefEq.beta.
        self.add_definition(SpecDefinition {
            name: "typed_def_eq_to_def_eq".to_string(),
            type_src: "forall (e : KExpr) (e' : KExpr), TypedDefEq e e' -> DefEq e e'".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (e' : KExpr) (h : TypedDefEq e e') => ",
                    "TypedDefEq.rec ",
                    // Motive: P(a, b, _) = DefEq a b
                    "(fun (a : KExpr) (b : KExpr) (_h : TypedDefEq a b) => DefEq a b) ",
                    // Case: refl
                    "(fun (a : KExpr) => DefEq.refl a) ",
                    // Case: symm
                    "(fun (a : KExpr) (b : KExpr) (_h : TypedDefEq a b) ",
                    "(ih : DefEq a b) => DefEq.symm a b ih) ",
                    // Case: trans
                    "(fun (a : KExpr) (b : KExpr) (c : KExpr) ",
                    "(_hab : TypedDefEq a b) (_hbc : TypedDefEq b c) ",
                    "(ih_ab : DefEq a b) (ih_bc : DefEq b c) => ",
                    "DefEq.trans a b c ih_ab ih_bc) ",
                    // Case: beta — TypedDefEq.beta still carries typing premises, but
                    // raw DefEq.beta is now UNTYPED, so drop them in the bridge.
                    "(fun (A : KExpr) (body : KExpr) (arg : KExpr) ",
                    "(_B : KExpr) (_u : Level) ",
                    "(_hA : Typing A (KExpr.sort _u)) ",
                    "(_hbody : Typing body _B) ",
                    "(_harg : Typing arg A) => ",
                    "DefEq.beta A body arg) ",
                    // Case: app_cong
                    "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
                    "(_hf : TypedDefEq f f') (_ha : TypedDefEq a a') ",
                    "(ih_f : DefEq f f') (ih_a : DefEq a a') => ",
                    "DefEq.app_cong f f' a a' ih_f ih_a) ",
                    // Case: lam_cong
                    "(fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) ",
                    "(_hA : TypedDefEq A A') (_hb : TypedDefEq b b') ",
                    "(ih_A : DefEq A A') (ih_b : DefEq b b') => ",
                    "DefEq.lam_cong A A' b b' ih_A ih_b) ",
                    // Case: pi_cong
                    "(fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr) ",
                    "(_hA : TypedDefEq A A') (_hB : TypedDefEq B B') ",
                    "(ih_A : DefEq A A') (ih_B : DefEq B B') => ",
                    "DefEq.pi_cong A A' B B' ih_A ih_B) ",
                    // Case: delta
                    "(fun (ed : KExpr) (ed' : KExpr) (hd : delta_reduces ed ed') => ",
                    "DefEq.delta ed ed' hd) ",
                    // Case: iota
                    "(fun (ei : KExpr) (ei' : KExpr) (hi : iota_reduces ei ei') => ",
                    "DefEq.iota ei ei' hi) ",
                    // Conclusion
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "One-way bridge: every TypedDefEq witness yields a raw DefEq witness. ",
                "Proof by TypedDefEq.rec mapping each constructor to its raw counterpart. ",
                "The beta case passes typing premises through to raw DefEq.beta. ",
                "DerivedProved: all deps are FoundationalRules. Part of #2872."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "TypedDefEq.rec".to_string(),
                "DefEq.refl".to_string(),
                "DefEq.symm".to_string(),
                "DefEq.trans".to_string(),
                "DefEq.beta".to_string(),
                "DefEq.app_cong".to_string(),
                "DefEq.lam_cong".to_string(),
                "DefEq.pi_cong".to_string(),
                "DefEq.delta".to_string(),
                "DefEq.iota".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Forward bridge raw_to_typed_def_eq (DefEq → TypedDefEq) is RETIRED:
        // under untyped DefEq.beta it is provably underivable (its beta arm cannot
        // synthesize TypedDefEq.beta's typing premises). All former consumers feed
        // the now-untyped Typing.conv directly with the raw DefEq.
        // (church_rosser_whnf retirement track.)

        // =========================================================
        // typing_is_def_eq: reducible alias for the conversion surface
        // =========================================================

        // typing_is_def_eq: the typed equality alias consumed by Typing.conv
        // and the type-preservation chain. Registered as reducible so the kernel
        // can unfold typing_is_def_eq ↔ TypedDefEq during type checking.
        // Part of #2872.
        self.add_definition_reducible(SpecDefinition {
            name: "typing_is_def_eq".to_string(),
            type_src: "KExpr -> KExpr -> Type".to_string(),
            value_src: Some("fun (a : KExpr) (b : KExpr) => TypedDefEq a b".to_string()),
            is_axiom: false,
            description: concat!(
                "Typed conversion equality (alias): typing_is_def_eq a b := TypedDefEq a b. ",
                "Consumed by Typing.conv and the type-preservation chain. ",
                "Reducible for kernel unfolding. Part of #2872."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_typing_conv_and_rec()?;

        Ok(())
    }
}
