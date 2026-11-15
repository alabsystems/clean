// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The view is a RETRACTION — bounding the store-side residual.**
//!
//! `docs/CRYSTAL_STATUS.md` names one residual at the load/store adequacy
//! boundary: a store of a RAW WORD at an encoded type, where "memory would then
//! hold a word the load images, so store-then-load would be the view rather than
//! the identity, and a store-side LOWERING -- the inverse of `ir_view_word`,
//! which no row carries -- would be needed to close it".
//!
//! Read against the definitions, the images (`ir_niche_image`, `ir_wrap_image`)
//! are the IDENTITY on `aggv` and on every non-word scalar, and send `int_` /
//! `ptr_` / `nullptr_` INTO `aggv`. So the image's range is exactly its fixed
//! points, which makes it idempotent -- and that bounds the residual at ONE
//! application rather than leaving it unbounded drift. Whether an inverse also
//! exists is a separate question this file does not answer.

use crate::spec::Specification;

impl Specification {
    /// Rows measuring whether the view is idempotent. See the module doc.
    #[cfg(test)]
    pub(super) fn evalir_view_retraction_rows() -> Vec<(String, String)> {
        vec![
            (
                // Is `ir_wrap_image` IDEMPOTENT? Twelve arms, every one expected
                // to be `Eq.refl`: the image is the identity on `aggv` and on
                // every non-word scalar, and `int_` / `ptr_` / `nullptr_` land IN
                // `aggv`, so a second application has nothing left to do. The two
                // payloads are DIFFERENT on purpose -- the outer application sees
                // a payload computed from the already-imaged word -- and the point
                // is that the `aggv` arm discards it.
                // Classified after the run.
                "ir_wrap_image_idem".to_string(),
                "def ir_wrap_image_idem (p1 : IRScalar) (p2 : IRScalar) (i : Nat) (c : Nat) (v : IRScalar) : Eq IRScalar (ir_wrap_image p2 i c (ir_wrap_image p1 i c v)) (ir_wrap_image p1 i c v) := IRScalar.rec (fun (x : IRScalar) => Eq IRScalar (ir_wrap_image p2 i c (ir_wrap_image p1 i c x)) (ir_wrap_image p1 i c x)) (Eq.refl IRScalar IRScalar.undef_) (fun (b : Bool) => Eq.refl IRScalar (IRScalar.bool_ b)) (fun (n : Nat) => Eq.refl IRScalar (IRScalar.aggv (ir_spine_with_slot i c p1))) (fun (n : Nat) => Eq.refl IRScalar (IRScalar.float_ n)) (Eq.refl IRScalar IRScalar.unit_) (fun (a : Nat) => Eq.refl IRScalar (IRScalar.aggv (ir_spine_with_slot i c p1))) (Eq.refl IRScalar (IRScalar.aggv (ir_spine_with_slot i c p1))) (fun (d : Nat) (md : Nat) => Eq.refl IRScalar (IRScalar.fat_ d md)) (fun (f : Nat) => Eq.refl IRScalar (IRScalar.fnptr_ f)) (fun (sp : IRScalar) (_ih : Eq IRScalar (ir_wrap_image p2 i c (ir_wrap_image p1 i c sp)) (ir_wrap_image p1 i c sp)) => Eq.refl IRScalar (IRScalar.aggv sp)) (Eq.refl IRScalar IRScalar.vnil) (fun (x : IRScalar) (rest : IRScalar) (_ihx : Eq IRScalar (ir_wrap_image p2 i c (ir_wrap_image p1 i c x)) (ir_wrap_image p1 i c x)) (_ihr : Eq IRScalar (ir_wrap_image p2 i c (ir_wrap_image p1 i c rest)) (ir_wrap_image p1 i c rest)) => Eq.refl IRScalar (IRScalar.vcons x rest)) v"
                    .to_string(),
            ),
            (
                // The niche half, and it needs one thing the wrap half did not:
                // `ir_niche_image`'s `int_` and `ptr_` arms dispatch `Nat.rec` on
                // the WORD ITSELF -- zero takes the `none` image, a successor the
                // `some` image carrying the payload -- so at a symbolic word the
                // inner application is STUCK and the outer cannot match on it. A
                // nested `Nat.rec` per arm splits it; both branches land in `aggv`,
                // where the outer image is the identity.
                //
                // Worth recording from reading it: `IRScalar.int_ Nat.zero` and
                // `IRScalar.nullptr_` produce the SAME image. So `ir_view_word` is
                // not injective, and the two-sided inverse CRYSTAL_STATUS calls for
                // ("a store-side LOWERING -- the inverse of `ir_view_word`") cannot
                // exist for a niche row. Idempotence is the strengthening the
                // definitions actually permit.
                "ir_niche_image_idem".to_string(),
                "def ir_niche_image_idem (p1 : IRScalar) (p2 : IRScalar) (no : Nat) (so : Nat) (v : IRScalar) : Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so v)) (ir_niche_image p1 no so v) := IRScalar.rec (fun (x : IRScalar) => Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so x)) (ir_niche_image p1 no so x)) (Eq.refl IRScalar IRScalar.undef_) (fun (b : Bool) => Eq.refl IRScalar (IRScalar.bool_ b)) (fun (n : Nat) => Nat.rec (fun (k : Nat) => Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so (IRScalar.int_ k))) (ir_niche_image p1 no so (IRScalar.int_ k))) (Eq.refl IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ no) IRScalar.vnil))) (fun (k : Nat) (_ihk : Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so (IRScalar.int_ k))) (ir_niche_image p1 no so (IRScalar.int_ k))) => Eq.refl IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ so) (IRScalar.vcons p1 IRScalar.vnil)))) n) (fun (n : Nat) => Eq.refl IRScalar (IRScalar.float_ n)) (Eq.refl IRScalar IRScalar.unit_) (fun (a : Nat) => Nat.rec (fun (k : Nat) => Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so (IRScalar.ptr_ k))) (ir_niche_image p1 no so (IRScalar.ptr_ k))) (Eq.refl IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ no) IRScalar.vnil))) (fun (k : Nat) (_ihk : Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so (IRScalar.ptr_ k))) (ir_niche_image p1 no so (IRScalar.ptr_ k))) => Eq.refl IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ so) (IRScalar.vcons p1 IRScalar.vnil)))) a) (Eq.refl IRScalar (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ no) IRScalar.vnil))) (fun (d : Nat) (md : Nat) => Eq.refl IRScalar (IRScalar.fat_ d md)) (fun (f : Nat) => Eq.refl IRScalar (IRScalar.fnptr_ f)) (fun (sp : IRScalar) (_ih : Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so sp)) (ir_niche_image p1 no so sp)) => Eq.refl IRScalar (IRScalar.aggv sp)) (Eq.refl IRScalar IRScalar.vnil) (fun (x : IRScalar) (rest : IRScalar) (_ihx : Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so x)) (ir_niche_image p1 no so x)) (_ihr : Eq IRScalar (ir_niche_image p2 no so (ir_niche_image p1 no so rest)) (ir_niche_image p1 no so rest)) => Eq.refl IRScalar (IRScalar.vcons x rest)) v"
                    .to_string(),
            ),
            (
                // *** THE VIEW AT ONE ROW IS A RETRACTION. ***
                //
                //   ir_view_word rec2 e (ir_view_word rec1 e v)
                //     == ir_view_word rec1 e v
                //
                // The two `rec_` arguments are DIFFERENT on purpose: the outer
                // application sees a payload computed from the already-imaged word,
                // and the claim holds precisely because the `aggv` arm discards it.
                // A statement with one shared `rec_` would be weaker and would hide
                // that.
                //
                // What it buys, against the residual CRYSTAL_STATUS states: a store
                // of a raw word at an encoded type makes store-then-load "the view
                // rather than the identity" -- true, and now bounded at ONE
                // application rather than left as unbounded drift. It is not a
                // lowering and does not claim to be one.
                "ir_view_word_idem".to_string(),
                "def ir_view_word_idem (rec1 : IRTy -> IRScalar -> IRScalar) (rec2 : IRTy -> IRScalar -> IRScalar) (e : IREnc) (v : IRScalar) : Eq IRScalar (ir_view_word rec2 e (ir_view_word rec1 e v)) (ir_view_word rec1 e v) := IREnc.rec (fun (e0 : IREnc) => Eq IRScalar (ir_view_word rec2 e0 (ir_view_word rec1 e0 v)) (ir_view_word rec1 e0 v)) (fun (k : Nat) (no : Nat) (so : Nat) (p : IRTy) => ir_niche_image_idem (rec1 p v) (rec2 p (ir_niche_image (rec1 p v) no so v)) no so v) (fun (k : Nat) (i : Nat) (c : Nat) (p : IRTy) => ir_wrap_image_idem (rec1 p v) (rec2 p (ir_wrap_image (rec1 p v) i c v)) i c v) e"
                    .to_string(),
            ),
            (
                // The retraction across the TABLE LOOKUP. Shaped after
                // `ir_view_opt_agg` in `eval_ir_slot_lemmas.rs` rather than
                // invented: same `IROption.rec` on the stuck `ir_enc_find` result,
                // same two minors. The `none` arm is `Eq.refl v` because a type
                // with no row is viewed as itself at both applications; the `some`
                // arm is `ir_view_word_idem` at a shared `ih`.
                "ir_view_opt_idem".to_string(),
                "def ir_view_opt_idem (ih : IRTy -> IRScalar -> IRScalar) (v : IRScalar) (o : IROption IREnc) : Eq IRScalar (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) v (fun (e2 : IREnc) => ir_view_word ih e2 v) o) (fun (e : IREnc) => ir_view_word ih e (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) v (fun (e2 : IREnc) => ir_view_word ih e2 v) o)) o) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) v (fun (e2 : IREnc) => ir_view_word ih e2 v) o) := IROption.rec IREnc (fun (o0 : IROption IREnc) => Eq IRScalar (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) v (fun (e2 : IREnc) => ir_view_word ih e2 v) o0) (fun (e : IREnc) => ir_view_word ih e (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) v (fun (e2 : IREnc) => ir_view_word ih e2 v) o0)) o0) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) v (fun (e2 : IREnc) => ir_view_word ih e2 v) o0)) (Eq.refl IRScalar v) (fun (e : IREnc) => ir_view_word_idem ih ih e v) o"
                    .to_string(),
            ),
            (
                // *** THE VIEW AT A TYPE IS A RETRACTION, at EVERY fuel and
                //     EVERY type. ***
                //
                // The induction hypothesis is UNUSED, and that is the content
                // rather than an accident — exactly as in `ir_view_ty_agg`, whose
                // shape this follows. The view at fuel `k+1` reaches the view at
                // `k` only INSIDE `ir_view_word`, and idempotence there is already
                // established for an arbitrary `rec_`, so no fact about the
                // shallower view is needed. Out of fuel is the identity, which is
                // idempotent for free.
                "ir_view_ty_idem".to_string(),
                "def ir_view_ty_idem (encs : IRList IREnc) (v : IRScalar) : forall (n : Nat) (t : IRTy), Eq IRScalar (ir_view_ty encs n t (ir_view_ty encs n t v)) (ir_view_ty encs n t v) := Nat.rec (fun (k : Nat) => forall (t : IRTy), Eq IRScalar (ir_view_ty encs k t (ir_view_ty encs k t v)) (ir_view_ty encs k t v)) (fun (t : IRTy) => Eq.refl IRScalar v) (fun (k : Nat) (_ih : forall (t : IRTy), Eq IRScalar (ir_view_ty encs k t (ir_view_ty encs k t v)) (ir_view_ty encs k t v)) (t : IRTy) => ir_view_opt_idem (ir_view_ty encs k) v (ir_enc_find encs t))"
                    .to_string(),
            ),
            (
                // Over a STEP RESULT. Two arms: a fault is unchanged at both
                // applications, and a value carries `ir_view_word_idem` under
                // `IRStepResult.value`. The fuel handed to the payload view is the
                // table's own length, which is the same at both applications --
                // that is why one `Eq.cong` suffices and no fuel reasoning
                // appears.
                "ir_view_result_idem".to_string(),
                "def ir_view_result_idem (encs : IRList IREnc) (e : IREnc) (r : IRStepResult) : Eq IRStepResult (ir_view_result encs e (ir_view_result encs e r)) (ir_view_result encs e r) := IRStepResult.rec (fun (r0 : IRStepResult) => Eq IRStepResult (ir_view_result encs e (ir_view_result encs e r0)) (ir_view_result encs e r0)) (fun (v : IRScalar) => Eq.cong IRScalar IRStepResult (fun (x : IRScalar) => IRStepResult.value x) (ir_view_word (ir_view_ty encs (ir_enc_len encs)) e (ir_view_word (ir_view_ty encs (ir_enc_len encs)) e v)) (ir_view_word (ir_view_ty encs (ir_enc_len encs)) e v) (ir_view_word_idem (ir_view_ty encs (ir_enc_len encs)) (ir_view_ty encs (ir_enc_len encs)) e v)) (fun (o : IROutcome) => Eq.refl IRStepResult (IRStepResult.fault o)) r"
                    .to_string(),
            ),
            (
                // Across the table lookup on the RESULT side, shaped after
                // `ir_load_view_opt_agg` beside it. `ir_load_view` branches on the
                // TABLE first and the result second; this follows that order, so
                // the `none` arm is `Eq.refl r` -- a type with no row is loaded as
                // itself.
                "ir_load_view_opt_idem".to_string(),
                "def ir_load_view_opt_idem (encs : IRList IREnc) (r : IRStepResult) (o : IROption IREnc) : Eq IRStepResult (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) r (fun (e2 : IREnc) => ir_view_result encs e2 r) o) (fun (e : IREnc) => ir_view_result encs e (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) r (fun (e2 : IREnc) => ir_view_result encs e2 r) o)) o) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) r (fun (e2 : IREnc) => ir_view_result encs e2 r) o) := IROption.rec IREnc (fun (o0 : IROption IREnc) => Eq IRStepResult (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) r (fun (e2 : IREnc) => ir_view_result encs e2 r) o0) (fun (e : IREnc) => ir_view_result encs e (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) r (fun (e2 : IREnc) => ir_view_result encs e2 r) o0)) o0) (IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) r (fun (e2 : IREnc) => ir_view_result encs e2 r) o0)) (Eq.refl IRStepResult r) (fun (e : IREnc) => ir_view_result_idem encs e r) o"
                    .to_string(),
            ),
            (
                // *** THE LOAD VIEW IS A RETRACTION. *** One line, because
                // `ir_load_view` IS the option recursion above at
                // `ir_enc_find encs t` -- the same one-line assembly
                // `ir_load_view_agg` uses.
                //
                // This is the level the store-side residual is stated at: a store
                // of a raw word at an encoded type makes store-then-load the VIEW
                // rather than the identity, and that view is now known to be
                // idempotent, so the discrepancy cannot compound across repeated
                // store/load round trips. It is a bound on the residual, not a
                // discharge of it.
                "ir_load_view_idem".to_string(),
                "def ir_load_view_idem (encs : IRList IREnc) (t : IRTy) (r : IRStepResult) : Eq IRStepResult (ir_load_view encs t (ir_load_view encs t r)) (ir_load_view encs t r) := ir_load_view_opt_idem encs r (ir_enc_find encs t)"
                    .to_string(),
            ),
        ]
    }
}
