// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **ALGORITHMIC IMPLIES DECLARATIVE, at the fixed environment.**
//!
//! ```text
//! KernelInfers tenv G e T -> TypingCtxConv tenv G e T
//! ```
//!
//! `KernelInfers` carries its operational steps as WITNESSED FIELDS — `whnf_to`
//! on the `pi`/`lam`/`app`/`let_` arms, `DefEq` on `app`/`let_`.
//! `TypingCtxConv` has no such fields and an UNRESTRICTED `conv` instead. So
//! this direction is exactly the act of ABSORBING the operational content into
//! `conv`, one arm at a time, and `whnf_to_preserves_def_eq` is the only
//! enabler it needs.
//!
//! # Why it is worth having
//!
//! With it, `impl_infer_sound` becomes a CONSEQUENCE of
//! `impl_infer_kinfers_sound` rather than an independently maintained twin: the
//! sharp theorem composed with this bridge IS the weak one. That makes the two
//! lanes provably coherent, and it makes precise the sense in which the sharp
//! codomain is stronger — it is stronger by exactly the content `conv` throws
//! away.
//!
//! It also closes an asymmetry. `kernel_infers_in_sound` (`acceptance_in.rs`)
//! has proved this for the ENV-PARAMETERISED variants `KernelInfersIn` /
//! `TypingCtxConvIn` since before the fixed-env pair existed; the fixed-env
//! statement was simply never written. This is that statement, and its minors
//! are the `*In` ones with the environment specialised and the level-semantics
//! detour dropped — the fixed-env `pi` arm concludes at `Level.imax` directly,
//! so it needs no outer `conv` where the `*In` arm needs one for `levelEqSem`.
//!
//! # Scope
//!
//! This relates two MODEL relations. It says nothing about the Rust checker,
//! and composing it with `impl_infer_kinfers_sound` yields a statement about
//! `ImplInfer`, which is itself a hand-transcribed model. Certificate §5 is the
//! standing statement of that gap.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The bridge. Nine minors, one per `KernelInfers` constructor.
    ///
    /// Recursor convention, read off `kernel_infers_in_sound` rather than
    /// guessed: each minor takes ALL constructor arguments in order — the
    /// recursive premises included — and then the induction hypotheses appended
    /// at the END, not interleaved.
    pub(super) fn kernel_infers_sound_src() -> String {
        let motive = "(fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) \
                      (_h : KernelInfers tenv G0 e0 T0) => TypingCtxConv tenv G0 e0 T0)";
        let cons_a = "(@ListType.cons KExpr A G0)";
        format!(
            "def kernel_infers_sound (tenv : KDeclEnv) (G : ListType KExpr) \
             (e : KExpr) (T : KExpr) (h : KernelInfers tenv G e T) : \
             TypingCtxConv tenv G e T := \
             @KernelInfers.rec tenv {motive} \
             (fun (G0 : ListType KExpr) (n : Level) => @TypingCtxConv.sort tenv G0 n) \
             (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr) \
             (get : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) => \
             @TypingCtxConv.var tenv G0 i A get) \
             (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (n : Level) \
             (SB : KExpr) (m : Level) \
             (_hA : KernelInfers tenv G0 A SA) (hwa : whnf_to SA (KExpr.sort n)) \
             (_hB : KernelInfers tenv {cons_a} B SB) (hwb : whnf_to SB (KExpr.sort m)) \
             (ihA : TypingCtxConv tenv G0 A SA) \
             (ihB : TypingCtxConv tenv {cons_a} B SB) => \
             @TypingCtxConv.pi tenv G0 A B n m \
             (@TypingCtxConv.conv tenv G0 A SA (KExpr.sort n) ihA \
             (whnf_to_preserves_def_eq SA (KExpr.sort n) hwa)) \
             (@TypingCtxConv.conv tenv {cons_a} B SB (KExpr.sort m) ihB \
             (whnf_to_preserves_def_eq SB (KExpr.sort m) hwb))) \
             (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) \
             (u : Level) \
             (_hA : KernelInfers tenv G0 A SA) (hwa : whnf_to SA (KExpr.sort u)) \
             (_hb : KernelInfers tenv {cons_a} b B) \
             (ihA : TypingCtxConv tenv G0 A SA) \
             (ihb : TypingCtxConv tenv {cons_a} b B) => \
             @TypingCtxConv.lam tenv G0 A b B u \
             (@TypingCtxConv.conv tenv G0 A SA (KExpr.sort u) ihA \
             (whnf_to_preserves_def_eq SA (KExpr.sort u) hwa)) ihb) \
             (fun (G0 : ListType KExpr) (nm : Name) (us : ListType Level) (A : KExpr) \
             (get : @Eq (OptionType KExpr) (kdecl_type_at tenv nm us) \
             (@OptionType.some KExpr A)) => @TypingCtxConv.const tenv G0 nm us A get) \
             (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) \
             (B : KExpr) (A2 : KExpr) \
             (_hf : KernelInfers tenv G0 f F) (hwF : whnf_to F (KExpr.pi A B)) \
             (_ha : KernelInfers tenv G0 a A2) (hde : DefEq A2 A) \
             (ihf : TypingCtxConv tenv G0 f F) \
             (iha : TypingCtxConv tenv G0 a A2) => \
             @TypingCtxConv.app tenv G0 f a A B \
             (@TypingCtxConv.conv tenv G0 f F (KExpr.pi A B) ihf \
             (whnf_to_preserves_def_eq F (KExpr.pi A B) hwF)) \
             (@TypingCtxConv.conv tenv G0 a A2 A iha hde)) \
             (fun (G0 : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) \
             (u : Level) (Tv : KExpr) (B : KExpr) \
             (_hty : KernelInfers tenv G0 ty Ty) (hwTy : whnf_to Ty (KExpr.sort u)) \
             (_hv : KernelInfers tenv G0 v Tv) (hdev : DefEq Tv ty) \
             (_hb : KernelInfers tenv (@ListType.cons KExpr ty G0) b B) \
             (ihty : TypingCtxConv tenv G0 ty Ty) \
             (ihv : TypingCtxConv tenv G0 v Tv) \
             (ihb : TypingCtxConv tenv (@ListType.cons KExpr ty G0) b B) => \
             @TypingCtxConv.let_ tenv G0 ty v b B u \
             (@TypingCtxConv.conv tenv G0 ty Ty (KExpr.sort u) ihty \
             (whnf_to_preserves_def_eq Ty (KExpr.sort u) hwTy)) \
             (@TypingCtxConv.conv tenv G0 v Tv ty ihv hdev) ihb) \
             (fun (G0 : ListType KExpr) (n : Nat) => @TypingCtxConv.lit_nat tenv G0 n) \
             (fun (G0 : ListType KExpr) (n : Nat) => @TypingCtxConv.lit_string tenv G0 n) \
             G e T h"
        )
    }

    /// **NON-VACUITY for the sharp theorem.** `impl_infer_kinfers_sound`, RUN.
    ///
    /// A layer-1 `ImplInfer` derivation goes in and a real `KernelInfers`
    /// derivation comes out, with every hypothesis discharged by a witness
    /// rather than assumed — `tenvrepc_empty` for the environment,
    /// `ctx_rep_nil_witness` for the context, `impl_sound_guard_witness` for the
    /// guard.
    ///
    /// **This is the check I spent the session demanding of other people's
    /// theorems and had not applied to my own.** A conditional theorem whose
    /// premises cannot be satisfied passes the axiom census, the domain-axiom
    /// count and the DerivedProved-debt count while looking green; that is the
    /// loop-(i) precedent and the open `CandModel` question. `impl_infer_sound`
    /// has carried such a witness since M4. The sharp theorem landed without
    /// one, which made it exactly the shape I had been flagging elsewhere.
    ///
    /// The derivation is written OUT rather than named, for the reason
    /// `add_sound_witnesses` records: `ImplSoundGuard` recurses on the
    /// DERIVATION via `ImplInfer.rec`, so it ι-reduces only against a literal
    /// constructor application.
    pub(super) fn impl_infer_kinfers_sound_witness_src() -> String {
        let tenv = "(fun (nm : Name) => @OptionType.none ImplConstInfo)";
        let tenvk = "(fun (nm : Name) => @OptionType.none KConstSig)";
        format!(
            "def impl_infer_kinfers_sound_witness : \
             KernelInfers {tenvk} (@ListType.nil KExpr) (KExpr.sort Level.zero) \
             (KExpr.sort (Level.succ Level.zero)) := \
             impl_infer_kinfers_sound {tenv} {tenvk} (@ListType.nil Name) tenvrepc_empty \
             Nat.zero LCtx.nil (ImplExpr.sort Level.zero) \
             (ImplExpr.sort (Level.succ Level.zero)) Nat.zero \
             (@ImplInfer.sort {tenv} (@ListType.nil Name) Nat.zero LCtx.nil Level.zero \
             (@Eq.refl Bool Bool.true)) \
             impl_sound_guard_witness (@ListType.nil Nat) (@ListType.nil KExpr) \
             ctx_rep_nil_witness"
        )
    }

    /// **THE COHERENCE FACT, as a term rather than as prose.**
    ///
    /// `impl_infer_sound`'s statement, proved by COMPOSITION:
    ///
    /// ```text
    /// impl_infer_kinfers_sound  then  kernel_infers_sound
    /// ```
    ///
    /// Four lines where `impl_infer_sound`'s own proof is a 194-line
    /// `ImplInfer.rec`. That M4's headline is derivable this way is the precise
    /// sense in which the sharp codomain is STRONGER: everything the weak
    /// theorem says is recoverable by discarding operational content into
    /// `conv`, and nothing recovers the sharp one from the weak.
    ///
    /// **Why `impl_infer_sound` is not simply RE-BODIED to this.** It could be,
    /// and the tree would lose 194 lines. But its nine `impl_sound_*` arms
    /// would then have no caller, and this repo's landing rule is that a
    /// capability without its caller does not stay. Deleting them is step M7 of
    /// `designs/2026-07-29-unified-implinfer-relation.md`, which is an owner
    /// decision about retiring a lane and not a tidying pass. So this is
    /// registered BESIDE the existing proof, which is the honest form: the
    /// derivability is checked, and nothing is removed on my judgement.
    pub(super) fn impl_infer_sound_via_kinfers_src() -> String {
        "def impl_infer_sound_via_kinfers \
         (tenv : Name -> OptionType ImplConstInfo) (tenvK : KDeclEnv) \
         (lps : ListType Name) (te : TEnvRepC tenv tenvK) \
         (n : Nat) (G : LCtx) (e : ImplExpr) (T : ImplExpr) (m : Nat) \
         (h : ImplInfer tenv lps n G e T m) \
         (g : ImplSoundGuard tenv lps n G e T m h) \
         (rho : ListType Nat) (Gk : ListType KExpr) (c : CtxRep Gk rho G) : \
         TypingCtxConv tenvK Gk (to_kexpr e rho) (to_kexpr T rho) := \
         kernel_infers_sound tenvK Gk (to_kexpr e rho) (to_kexpr T rho) \
         (impl_infer_kinfers_sound tenv tenvK lps te n G e T m h g rho Gk c)"
            .to_string()
    }

    /// Measured green in scratch 2026-09-18 (0.7 s), then wired.
    pub(super) fn kinfers_declarative_sources() -> Vec<(String, String)> {
        vec![
            (
                "kernel_infers_sound".to_string(),
                Self::kernel_infers_sound_src(),
            ),
            (
                "impl_infer_sound_via_kinfers".to_string(),
                Self::impl_infer_sound_via_kinfers_src(),
            ),
            (
                "impl_infer_kinfers_sound_witness".to_string(),
                Self::impl_infer_kinfers_sound_witness_src(),
            ),
        ]
    }
    /// Registered after `add_implementation_soundness_whnf_decomposition`, which
    /// mints the single enabler `whnf_to_preserves_def_eq`. `KernelInfers` and
    /// `TypingCtxConv` come far earlier, with `add_dependent_sn_richmodel`.
    pub(super) fn add_kinfers_declarative(&mut self) -> Result<(), SpecError> {
        for (_n, src) in Self::kinfers_declarative_sources() {
            self.add_recursive_def(&src, "algorithmic implies declarative")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "kinfers_declarative_tests.rs"]
mod tests;
