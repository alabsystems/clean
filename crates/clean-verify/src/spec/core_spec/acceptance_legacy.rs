// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One-way compatibility with the additive semantic acceptance judgments.
//!
//! The legacy relations remain unchanged. Their fixed-environment derivations
//! embed structurally into the new relations at exactly `the_red_env`; there
//! is no reverse embedding, common-reduct premise, or confluence assumption.
//! This inclusion concerns model judgments, not extracted Rust acceptance.
//!
//! Proof-development check: 557 dependency declarations copied from the actual
//! 31fa57c00 Wgxf0r export (SHA256
//! 941dcfb5f386a75f80afef5afc35dfc733e1fde210abea22bbf8ae3333478957),
//! including the actual reflected the_red_env, followed by the intended new
//! semantic relation/judgment definitions and these seven proof terms. Pinned
//! Lean 4.30.0-rc2 accepted all seven with empty axiom closures on 2026-09-08
//! (0.88 seconds, 561,496,064-byte max RSS; 1 GB reserved). This scratch check
//! precedes and does not replace registered Clean checking and full replay.

use crate::spec::error::SpecError;
use crate::spec::Specification;

use super::acceptance_in::theorem;

const CONVERSION_TYPE: &str =
    "forall (e : KExpr) (e' : KExpr), DefEq e e' -> DefEqIn the_red_env e e'";

const CONVERSION_PROOF: &str = r"fun (e : KExpr) (e' : KExpr) (h : DefEq e e') =>
DefEq.rec
  (fun (x : KExpr) (y : KExpr) (_h : DefEq x y) => DefEqIn the_red_env x y)
  (fun (x : KExpr) => DefEqIn.refl the_red_env x)
  (fun (x : KExpr) (y : KExpr) (_h : DefEq x y) (ih : DefEqIn the_red_env x y) =>
    DefEqIn.symm the_red_env x y ih)
  (fun (x : KExpr) (y : KExpr) (z : KExpr) (_hxy : DefEq x y) (_hyz : DefEq y z)
    (ihxy : DefEqIn the_red_env x y) (ihyz : DefEqIn the_red_env y z) =>
    DefEqIn.trans the_red_env x y z ihxy ihyz)
  (fun (A : KExpr) (b : KExpr) (a : KExpr) =>
    DefEqIn.raw the_red_env (KExpr.app (KExpr.lam A b) a) (instantiate b a)
      (par_reduces_cd.beta the_red_env A A b b a a
        (par_reduces_cd.refl the_red_env A) (par_reduces_cd.refl the_red_env b)
        (par_reduces_cd.refl the_red_env a)))
  (fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr)
    (_hf : DefEq f f') (_ha : DefEq a a')
    (ihf : DefEqIn the_red_env f f') (iha : DefEqIn the_red_env a a') =>
    DefEqIn.app the_red_env f f' a a' ihf iha)
  (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr)
    (_hA : DefEq A A') (_hb : DefEq b b')
    (ihA : DefEqIn the_red_env A A') (ihb : DefEqIn the_red_env b b') =>
    DefEqIn.lam the_red_env A A' b b' ihA ihb)
  (fun (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr)
    (_hA : DefEq A A') (_hB : DefEq B B')
    (ihA : DefEqIn the_red_env A A') (ihB : DefEqIn the_red_env B B') =>
    DefEqIn.pi the_red_env A A' B B' ihA ihB)
  (fun (x : KExpr) (y : KExpr) (hd : delta_reduces x y) =>
    DefEqIn.raw the_red_env x y
      (par_reduces_cd.delta the_red_env x y (delta_reduces_to_step x y hd)))
  (fun (x : KExpr) (y : KExpr) (hi : iota_reduces x y) =>
    DefEqIn.raw the_red_env x y
      (par_reduces_cd.iota the_red_env x y (iota_reduces_to_step x y hi)))
  (fun (A : KExpr) (v : KExpr) (b : KExpr) =>
    DefEqIn.raw the_red_env (KExpr.let_ A v b) (instantiate b v)
      (par_reduces_cd.let_ the_red_env A A v v b b
        (par_reduces_cd.refl the_red_env A) (par_reduces_cd.refl the_red_env v)
        (par_reduces_cd.refl the_red_env b)))
  (fun (A : KExpr) (A' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr)
    (_hA : DefEq A A') (_hv : DefEq v v') (_hb : DefEq b b')
    (ihA : DefEqIn the_red_env A A') (ihv : DefEqIn the_red_env v v')
    (ihb : DefEqIn the_red_env b b') =>
    DefEqIn.let_ the_red_env A A' v v' b b' ihA ihv ihb)
  (fun (n : Name) (i : Nat) (x : KExpr) (y : KExpr) (_h : DefEq x y)
    (ih : DefEqIn the_red_env x y) => DefEqIn.proj the_red_env n i x y ih)
  e e' h";

const TYPING_TYPE: &str = "forall (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), TypingCtxConv tenv G e T -> TypingCtxConvIn the_red_env tenv G e T";

const TYPING_PROOF: &str = r"fun (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : TypingCtxConv tenv G e T) =>
TypingCtxConv.rec tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
    (_h : TypingCtxConv tenv G0 e0 T0) => TypingCtxConvIn the_red_env tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
    (get : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) =>
    TypingCtxConvIn.var the_red_env tenv G0 i A get)
  (fun (G0 : ListType KExpr) (u : Level) => TypingCtxConvIn.sort the_red_env tenv G0 u)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
    (_hA : TypingCtxConv tenv G0 A (KExpr.sort u))
    (_hB : TypingCtxConv tenv (ListType.cons KExpr A G0) B (KExpr.sort v))
    (ihA : TypingCtxConvIn the_red_env tenv G0 A (KExpr.sort u))
    (ihB : TypingCtxConvIn the_red_env tenv (ListType.cons KExpr A G0) B (KExpr.sort v)) =>
    TypingCtxConvIn.pi the_red_env tenv G0 A B u v ihA ihB)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
    (_hA : TypingCtxConv tenv G0 A (KExpr.sort u))
    (_hb : TypingCtxConv tenv (ListType.cons KExpr A G0) b B)
    (ihA : TypingCtxConvIn the_red_env tenv G0 A (KExpr.sort u))
    (ihb : TypingCtxConvIn the_red_env tenv (ListType.cons KExpr A G0) b B) =>
    TypingCtxConvIn.lam the_red_env tenv G0 A b B u ihA ihb)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
    (_hf : TypingCtxConv tenv G0 f (KExpr.pi A B)) (_ha : TypingCtxConv tenv G0 a A)
    (ihf : TypingCtxConvIn the_red_env tenv G0 f (KExpr.pi A B))
    (iha : TypingCtxConvIn the_red_env tenv G0 a A) =>
    TypingCtxConvIn.app the_red_env tenv G0 f a A B ihf iha)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
    (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) =>
    TypingCtxConvIn.const the_red_env tenv G0 n us A get)
  (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr)
    (_he : TypingCtxConv tenv G0 e0 A) (heq : DefEq A B)
    (ihe : TypingCtxConvIn the_red_env tenv G0 e0 A) =>
    TypingCtxConvIn.conv the_red_env tenv G0 e0 A B ihe (def_eq_to_def_eq_in A B heq))
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
    (_hA : TypingCtxConv tenv G0 A (KExpr.sort u)) (_hv : TypingCtxConv tenv G0 v A)
    (_hb : TypingCtxConv tenv (ListType.cons KExpr A G0) b B)
    (ihA : TypingCtxConvIn the_red_env tenv G0 A (KExpr.sort u))
    (ihv : TypingCtxConvIn the_red_env tenv G0 v A)
    (ihb : TypingCtxConvIn the_red_env tenv (ListType.cons KExpr A G0) b B) =>
    TypingCtxConvIn.let_ the_red_env tenv G0 A v b B u ihA ihv ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => TypingCtxConvIn.lit_nat the_red_env tenv G0 n)
  (fun (G0 : ListType KExpr) (n : Nat) => TypingCtxConvIn.lit_string the_red_env tenv G0 n)
  G e T h";

impl Specification {
    /// Register after acceptance_in and the existing delta/iota witness bridges.
    pub(super) fn add_acceptance_legacy(&mut self) -> Result<(), SpecError> {
        theorem(
            self,
            "def_eq_to_def_eq_in",
            CONVERSION_TYPE,
            CONVERSION_PROOF,
            "One-way structural inclusion of all twelve legacy DefEq constructors at the same fixed the_red_env. Beta/zeta are genuine computational parallel steps with reflexive children; delta/iota project the actual stored step witnesses. No joinability, confluence, reverse embedding, or source-execution premise.",
        )?;
        theorem(
            self,
            "typingctxconv_to_typingctxconv_in",
            TYPING_TYPE,
            TYPING_PROOF,
            "One-way structural inclusion of all ten legacy declarative typing constructors, composing the checked conversion inclusion in the conv arm. The environment, context, expression and type are unchanged. No validity of arbitrary environments or production typing correspondence is inferred.",
        )?;
        for (name, type_src, value_src, description) in [
            (
                "acceptance_legacy_beta",
                "forall (A : KExpr) (b : KExpr) (a : KExpr), DefEqIn the_red_env (KExpr.app (KExpr.lam A b) a) (instantiate b a)",
                "fun (A : KExpr) (b : KExpr) (a : KExpr) => def_eq_to_def_eq_in (KExpr.app (KExpr.lam A b) a) (instantiate b a) (DefEq.beta A b a)",
                "An actual caller of the conversion embedding on the legacy beta constructor.",
            ),
            (
                "acceptance_legacy_zeta",
                "forall (A : KExpr) (v : KExpr) (b : KExpr), DefEqIn the_red_env (KExpr.let_ A v b) (instantiate b v)",
                "fun (A : KExpr) (v : KExpr) (b : KExpr) => def_eq_to_def_eq_in (KExpr.let_ A v b) (instantiate b v) (DefEq.zeta A v b)",
                "An actual caller of the conversion embedding on the legacy zeta constructor.",
            ),
            (
                "acceptance_legacy_conversion",
                "forall (tenv : KDeclEnv) (G : ListType KExpr), TypingCtxConvIn the_red_env tenv G (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))) (KExpr.sort Level.zero))",
                "fun (tenv : KDeclEnv) (G : ListType KExpr) => typingctxconv_to_typingctxconv_in tenv G (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))) (KExpr.sort Level.zero)) (TypingCtxConv.conv tenv G (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))) (KExpr.sort Level.zero)) (TypingCtxConv.sort tenv G Level.zero) (DefEq.symm (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero))) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero)) (DefEq.beta (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) (KExpr.sort Level.zero))))",
                "An inhabited legacy sort derivation converted by symmetric beta equality, passed through the actual typing inclusion. Exercises its conv branch and the composed conversion proof without assuming an input derivation.",
            ),
            (
                "acceptance_legacy_literal_nat",
                "forall (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat), TypingCtxConvIn the_red_env tenv G (literal_nat n) literal_nat_type",
                "fun (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat) => typingctxconv_to_typingctxconv_in tenv G (literal_nat n) literal_nat_type (TypingCtxConv.lit_nat tenv G n)",
                "An actual caller of the typing inclusion on every legacy Nat literal payload.",
            ),
            (
                "acceptance_legacy_literal_string",
                "forall (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat), TypingCtxConvIn the_red_env tenv G (literal_string n) literal_string_type",
                "fun (tenv : KDeclEnv) (G : ListType KExpr) (n : Nat) => typingctxconv_to_typingctxconv_in tenv G (literal_string n) literal_string_type (TypingCtxConv.lit_string tenv G n)",
                "An actual caller of the typing inclusion on every legacy String literal payload.",
            ),
        ] {
            theorem(self, name, type_src, value_src, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn legacy_acceptance_inclusions_are_checked_without_axioms() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "def_eq_to_def_eq_in",
            "typingctxconv_to_typingctxconv_in",
            "acceptance_legacy_beta",
            "acceptance_legacy_zeta",
            "acceptance_legacy_conversion",
            "acceptance_legacy_literal_nat",
            "acceptance_legacy_literal_string",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered actual proof");
            assert!(!definition.is_axiom);
            assert!(definition.elaborated_value.is_some());
            assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
        }
        // The compatibility layer is deliberately one-way. Its extra semantic
        // universe conversions do not imply legacy raw-syntax joinability.
        assert!(!super::CONVERSION_PROOF.contains("def_eq_joinable"));
        assert!(!super::TYPING_PROOF.contains("def_eq_joinable"));
    }
}
