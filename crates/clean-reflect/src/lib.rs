// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![forbid(unsafe_code)]
// EXHAUSTIVE DISPATCH, crate-wide. A catch-all arm over an enum compiles
// unchanged when the enum grows, so a variant trust-ir (or the kernel) adds
// would join a refusal -- or a handled arm -- that nobody decided it belongs
// to. Clippy denies the three spellings of that by TYPE, in every target of
// this crate (each integration test carries the same attribute, and
// `dispatch_exhaustive_tests` refuses a target root that drops it): a `_` or
// bare-binding arm over an enum, a wildcard standing for one variant, and a
// `_` inside an or-pattern. The full gate's `dispatch-exhaustive-lint` leg runs
// clippy on this crate with `-D warnings`, so the deny is enforced rather than
// advisory. It is a `deny`, not a `forbid`, so an item-level `#[allow]` /
// `#[expect]` overrides it (the syn helpers use one over syn's
// `#[non_exhaustive]` enums); for `Inst` dispatches `dispatch_exhaustive_tests`
// therefore refuses EVERY catch-all itself -- at top level, one level down
// inside a wrapper around the `Inst`, silenced or not.
//
// THREAT MODEL: accidental catch-alls in first-party code. Neither half is a
// defence against a deliberately obfuscated spelling (a variant named through
// `<() as SomeTrait>::I::Unreachable`, a proc macro, a `cfg`); those are code
// review's, and chasing them syntactically is a scan that never terminates.
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

//! # clean-reflect — the SemanticReflection map `<<.>> : trust-ir -> clean_kernel::Expr`
//!
//! GOAL: turn trust-ir obligations into honest CIC propositions the clean kernel
//! can prove. The reflector emits EXACTLY the `Expr` AST that the mechanized
//! proofs in `proofs/trust-soundness` already prove `PROVED => safe` over, so
//! the reflector's output INHERITS that soundness verbatim. Emit a different
//! shape and the proof does not apply.
//!
//! ## What `TrustLabel::Proven` means (intrinsic kernel discharge)
//!
//! The obligation is CONSTITUTIVE of the trust-ir object and is verified
//! INTRINSICALLY: the Clean kernel proves the object's OWN obligation via
//! `check_type(proof_term, goal)` — the de Bruijn criterion — under
//! [`Environment::with_prelude`] ONLY. It is NOT verified by synthesizing an
//! `Expr` and `is_def_eq`-comparing it against a hand-written external
//! `proofs/trust-soundness/overflow_trust_boundary.lean` used as a
//! per-obligation reference model. That separate-step / outside-model
//! antipattern has been RETIRED.
//!
//! The runnable end-to-end demonstration is `tests/fused_overflow.rs`: it
//! DERIVES the overflow obligation `Expr` from the real `trust_ir::InstrNode`'s
//! own fields (the type's modulus `2^bit_width(ty)`), and DISCHARGES it by
//! kernel-`check_type` against the object's negated goal. Mutating the SAME node
//! (`ty` U8 -> U64, or `op` Add -> Sub) moves BOTH the derived obligation and
//! the verdict — the obligation is inseparable from the object (CHANGE-COUPLED).
//!
//! Therefore `TrustLabel::Proven` means precisely: the obligation derived from
//! the trust-ir node was kernel-discharged (the kernel accepted a proof of the
//! object's own negated goal), MODULO the named `ayAddOverflows` (ay BV-overflow)
//! trust boundary. The grounding lemma `overflow_op_sound` (`∀ truePanic : Bool`)
//! applies to the emit by INSTANTIATION at `truePanic := ayAddOverflows a b`; the
//! soundness link is the once-proven meta-theorem `PROVED => safe` over the
//! kernel's verdict, NOT an external `.lean` re-consulted per obligation.
//!
//! The one remaining trust boundary is NAMED: `ayAddOverflows : Nat -> Nat ->
//! Bool` is ay's BV add-overflow decision over the operands (an `opaque`
//! declaration); clean does NOT prove `ayAddOverflows a b = decide (a+b >= 256)`
//! — that is ay's job, exactly like "ay's UNSAT is sound" in `search_soundness`.
//!
//! ## Fail-closed is mandatory outside Fragment-1
//!
//! Fragment-1 is exactly the set of constructs whose `PROVED => safe` is
//! mechanized today (arithmetic overflow/div/shift, index/memory bounds, guarded
//! straight-line asserts, modeled/fail-closed calls). Branching/CFG, loops,
//! recursion, atomics, closures, NN/borrow/RC, and the full memory model are
//! EXCLUDED. For any such construct the reflector returns
//! [`ReflectError::Unsupported`] (fail-closed) and NEVER emits a wrong or
//! placeholder `Expr`.
//!
//! Increment 1 (this crate's current emission contract) reflects ONE arithmetic
//! overflow obligation into `overflowObligation (ayAddOverflows a b)` over the
//! real Lean Names; the fused intrinsic discharge of an object-derived overflow
//! obligation by the kernel — and its change-coupling — is demonstrated in
//! `tests/fused_overflow.rs`.
//!
//! ## Fragment-2 — expression denotation ([`denote`])
//!
//! Fragment-1 reflects *obligations* (does this instruction panic?);
//! [`denote`] (Fragment-2) reflects *meaning*: it maps a compiled trust-ir
//! function AND the decl's original kernel definition into one shared
//! `Nat`-mod-`2^w` vocabulary so the kernel can DECIDE whether the emitted
//! code denotes the source. It backs the backend semantics-preservation
//! (translation-validation) certificate — see the [`denote`] module docs for
//! the exact fragment, the vocabulary, and its honestly-stated trust status.

pub mod boxed_entry;
pub mod denote;
mod error;
mod reflect;
pub mod source_equation;

#[cfg(test)]
mod anchor_env_tests;
#[cfg(test)]
mod dispatch_exhaustive_tests;
pub mod vocab;

pub use denote::{
    denote_function, denote_scalar_function, denote_source, denote_source_in_environment,
    denote_source_nat, denote_source_nat_in_environment, denote_source_with_requirements,
    heap_vocab_declarations, hempty, hread, hwrite, modulus, tv_proof_term, tv_statement,
    tv_statement_formula, tv_theorem_name, RecordVocab, ScalarDenotation, ScalarSort,
    SourceDenotation, TvDenotation, CLEAN_BACKEND_TV_ANCHOR, CLEAN_TV_FORMULA_SCHEMA, HEAP_HEMPTY,
    HEAP_HREAD, HEAP_HWRITE,
};
pub use error::ReflectError;
pub use reflect::{
    reflect_inst, reflect_module, LeanLemmaRef, ObligationOrigin, ReflectedModule,
    ReflectedObligation, TrustLabel,
};

use clean_kernel::{Declaration, Environment, Expr, Level, Name};

/// The kernel names of the four SIGNED CARRIER ALIASES, by width (WS1.15 S3).
pub const SIGNED_CARRIER_ALIASES: [(u32, &str); 4] = [
    (8, "CleanTV.Int8"),
    (16, "CleanTV.Int16"),
    (32, "CleanTV.Int32"),
    (64, "CleanTV.Int64"),
];

/// The four signed carrier aliases of the `clean_backend_tv` anchor
/// environment, reducible definitions
///
/// ```text
/// CleanTV.Int8 : Type := Nat    CleanTV.Int16 : Type := Nat
/// CleanTV.Int32 : Type := Nat   CleanTV.Int64 : Type := Nat
/// ```
///
/// The Clean-side MIRROR of trust-ir-build's
/// `clean_backend_tv::signed_carrier_declarations` (WS1.15 S3), whose
/// canonical-source note asks for exactly this: "clean-reflect must install
/// the same four definitions". Clean mints no signed shape yet (WS6.6 keeps
/// signed ops unminted), so no Clean statement mentions an alias. They are
/// installed because they are part of the anchor ENVIRONMENT the re-checker
/// builds, and a bound certificate names that environment by digest (roadmap
/// WS6.7(b)): an environment without them digests differently and is refused
/// as `CertificateBindingMismatch { field: "environment_digest" }`.
#[must_use]
pub fn signed_carrier_declarations() -> Vec<Declaration> {
    SIGNED_CARRIER_ALIASES
        .iter()
        .map(|(_, name)| Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::const_str(vocab::NAT),
            is_reducible: true,
        })
        .collect()
}

/// The environment every `clean_backend_tv` judgment runs in: the ground
/// prelude, then the Fragment-4 heap vocabulary ([`heap_vocab_declarations`]),
/// then the signed carrier aliases ([`signed_carrier_declarations`]) — BEFORE
/// any theorem is declared into it.
///
/// This is the Clean-side spelling of trust-ir-build's
/// `clean_backend_tv::anchor_environment`, declaration for declaration. It is
/// what the minter judges a translation equation in AND what a bound
/// certificate's `environment_digest` digests
/// (`trust_ir::proof::kernel_environment_digest`, WS6.7(b)), so the two cannot
/// name different environments. Drift from the re-checker's spelling is
/// fail-closed: the same certificate is then refused as a binding mismatch.
///
/// # Errors
///
/// A message naming the step that failed (the prelude, or one of the two
/// vocabularies refusing to install).
pub fn tv_anchor_environment() -> Result<Environment, String> {
    let mut env = Environment::try_with_prelude()
        .map_err(|e| format!("prelude environment failed: {e:?}"))?;
    for decl in heap_vocab_declarations() {
        env.add_decl(decl)
            .map_err(|e| format!("heap vocabulary failed to install: {e:?}"))?;
    }
    for decl in signed_carrier_declarations() {
        env.add_decl(decl)
            .map_err(|e| format!("signed carrier aliases failed to install: {e:?}"))?;
    }
    Ok(env)
}

/// Wrap an obligation *condition* `Expr` as the `not_fires` goal proposition —
/// "this obligation does not fire" (PROVED) — i.e. `@Eq.{1} Bool obligation
/// Bool.false` (spec Section 5.1). The result is a genuine kernel `Prop`,
/// type-checkable against the real (prelude-bearing) environment: `Eq` is the
/// polymorphic prelude `Eq : {α : Sort u} → α → α → Prop`, instantiated at
/// `α := Bool` (level `1`).
pub fn not_fires(obligation_expr: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string(vocab::eq_const()),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::const_str(vocab::NAT_BOOL_CARRIER),
            obligation_expr.clone(),
            Expr::const_str(vocab::bool_false_const()),
        ],
    )
}

/// Register every `%<id>` SSA operand symbol referenced by `reflected` into
/// `env` (carrier sort `Nat`), so each `obligation_expr` type-checks against it.
///
/// A convenience for callers that need each `obligation_expr` to type-check
/// against an [`Environment`] — the operand `%<id>` symbols are added as `Nat`
/// axioms. The intrinsic kernel discharge in `tests/fused_overflow.rs` models
/// operands as concrete `Nat` literals derived from the object instead, so it
/// needs no operand registration; this helper remains for env-based callers.
///
/// # Errors
///
/// Returns the kernel `EnvError` only on a duplicate operand symbol, which would
/// indicate a programming error in operand naming.
pub fn register_operands(
    env: &mut Environment,
    reflected: &ReflectedModule,
) -> Result<(), clean_kernel::KernelEnvError> {
    let mut seen = std::collections::BTreeSet::new();
    for ob in &reflected.obligations {
        for sym in operand_symbols(&ob.obligation_expr) {
            if seen.insert(sym.clone()) {
                vocab::register_operand(env, &sym)?;
            }
        }
    }
    Ok(())
}

/// Collect the `%<id>` operand constant names appearing in an obligation `Expr`.
#[must_use]
fn operand_symbols(expr: &Expr) -> Vec<String> {
    use clean_kernel::ExprKind;
    let mut out = Vec::new();
    let mut stack: Vec<&Expr> = vec![expr];
    // Two one-variant tests, not a dispatch: an obligation this crate emits is
    // an application spine over constants, and only those two shapes carry an
    // operand symbol or lead to one. Nothing else is descended into.
    while let Some(e) = stack.pop() {
        if let ExprKind::Const(name, _) = e.kind() {
            let s = name.to_string();
            if s.starts_with('%') {
                out.push(s);
            }
        } else if let ExprKind::App(f, a) = e.kind() {
            stack.push(f);
            stack.push(a);
        }
    }
    out
}
