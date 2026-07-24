// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # Give-back refinement anchor (M3, first certified instance)
//!
//! In-process kernel anchor for the `RustSem` give-back refinement — the analog
//! of [`Environment::init_nn_verify_farkas_constructive`]. It admits a genuine,
//! axiom-clean `Declaration::Theorem` whose proof TERM the trusted
//! `clean_kernel` type-checker re-checks in-process (no external prover) when a
//! `trust-ir` `ProofEvidence::CleanCic` carrying the
//! `KERNEL_ANCHOR_GIVEBACK_REFINEMENT` directive certifies a `GiveBackRefinement`
//! obligation (flipping it `Pending → Certified`, with Aeneas nowhere in the
//! trusted chain).
//!
//! First certified instance (the give-back plan's decidable subset, identity
//! case): the give-back lens ROUND-TRIP law for a no-op `&mut` — the identity
//! backward function returns exactly the (unchanged) borrowed value:
//! `RustSem.GiveBack.backId v = v`. Proved by `Eq.refl` (the kernel δ-unfolds
//! `backId` and β-reduces), so the theorem's transitive axiom closure contains
//! only the foundational `Eq.refl`. Richer refinement laws — over the full
//! `value_at_address::step` reflected in `clean-rust-sem` — extend this anchor
//! as they are mechanized.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Fully-qualified name of the give-back identity backward function.
pub const GIVEBACK_BACK_ID: &str = "RustSem.GiveBack.backId";
/// Fully-qualified name of the give-back round-trip law (the certified theorem).
pub const GIVEBACK_BACK_ID_ROUNDTRIPS: &str = "RustSem.GiveBack.backId_roundTrips";
/// Universe-POLYMORPHIC identity backward function: `backIdP.{u} {α : Type u} v = v`.
/// Lets an UNTOUCHED `&mut` of ANY type (struct/enum/…) certify, not just a scalar —
/// the identity analog of [`GIVEBACK_COND_SET_POLY`].
pub const GIVEBACK_BACK_ID_POLY: &str = "RustSem.GiveBack.backIdP";
/// Polymorphic round-trip law: `∀ {α} (v : α), backIdP v = v` (untouched, any type).
pub const GIVEBACK_BACK_ID_POLY_ROUNDTRIPS: &str = "RustSem.GiveBack.backIdP_roundTrips";
/// Fully-qualified name of the give-back backward function for `*x += 1`.
pub const GIVEBACK_INCR_BACK: &str = "RustSem.GiveBack.incrBack";
/// Fully-qualified name of the incr give-back lens-composition law (`∘ = +2`).
pub const GIVEBACK_INCR_COMPOSES: &str = "RustSem.GiveBack.incrBack_composes";
/// Fully-qualified name of the incr give-back triple-composition law (`∘∘∘ = +3`).
pub const GIVEBACK_INCR_THRICE: &str = "RustSem.GiveBack.incrBack_thrice";
/// The SINGLE-STEP give-back law: `∀ v, incrBack v = v + 1` — the law that actually
/// STATES the give-back of `*x += 1` (its backward function maps `v ↦ v+1`), as
/// opposed to the composition laws (`∘ = +2`, `∘∘∘ = +3`). This is the theorem a
/// give-back certificate for `*x += 1` should cite, so the cited theorem genuinely
/// expresses the function's give-back rather than an algebraic corollary.
pub const GIVEBACK_INCR_STEP: &str = "RustSem.GiveBack.incrBack_step";
/// The give-back backward function of a CONSTANT increment `*x += k` for ANY `k`:
/// `addKBack k v = v + k`. Parameterized by `k`, so ONE law covers every constant
/// increment (subsuming [`GIVEBACK_INCR_STEP`], the `k = 1` instance).
pub const GIVEBACK_ADD_K_BACK: &str = "RustSem.GiveBack.addKBack";
/// The parameterized step law: `∀ k v, addKBack k v = v + k` (the give-back of `*x += k`).
pub const GIVEBACK_ADD_K_STEP: &str = "RustSem.GiveBack.addKBack_step";
/// Fully-qualified name of the store read-after-write law.
pub const GIVEBACK_READ_AFTER_WRITE: &str = "RustSem.GiveBack.read_after_write";
/// Fully-qualified name of the VALUE-POLYMORPHIC read-after-write law
/// (`∀ (α : Type), …` — the give-back memory law for any value type; the
/// foundation for generic `&mut T`).
pub const GIVEBACK_READ_AFTER_WRITE_POLY: &str = "RustSem.GiveBack.read_after_write_poly";
/// Fully-qualified name of the store frame / non-interference law.
pub const GIVEBACK_FRAME: &str = "RustSem.GiveBack.frame";
/// Fully-qualified name of the incr give-back-over-store law.
pub const GIVEBACK_INCR_STORE: &str = "RustSem.GiveBack.incr_store";
/// Fully-qualified name of the faithful `u32` wrapping add (over the representation).
pub const GIVEBACK_U32_ADD: &str = "RustSem.GiveBack.u32Add";
/// Fully-qualified name of the `u32` give-back backward function.
pub const GIVEBACK_INCR_BACK_U32: &str = "RustSem.GiveBack.incrBackU32";
/// Fully-qualified name of the `u32` wraparound law: `incrBackU32 (u32::MAX) = 0`.
pub const GIVEBACK_INCR_U32_WRAPS: &str = "RustSem.GiveBack.incrBackU32_wraps";

// ── Aggregate give-back (a `&mut` into field 0 of a `(Nat, Nat)` pair) ────────
/// Forward function of a `&mut p.0` borrow: `aggFstFwd p = p.fst`.
pub const GIVEBACK_AGG_FST_FWD: &str = "RustSem.GiveBack.aggFstFwd";
/// Backward function of a `&mut p.0` borrow: `aggFstBack p v' = Prod.mk v' p.snd`
/// — reconstructs the whole aggregate with field 0 updated and field 1 framed.
pub const GIVEBACK_AGG_FST_BACK: &str = "RustSem.GiveBack.aggFstBack";
/// Lens law put-get: reading the field back yields exactly what was given back.
pub const GIVEBACK_AGG_PUT_GET: &str = "RustSem.GiveBack.aggFst_putGet";
/// Lens law get-put (round-trip via structure eta): giving back the value just
/// read reconstructs the original aggregate unchanged.
pub const GIVEBACK_AGG_GET_PUT: &str = "RustSem.GiveBack.aggFst_getPut";
/// Lens law frame: the give-back leaves the SIBLING field (`p.snd`) untouched.
pub const GIVEBACK_AGG_FRAME: &str = "RustSem.GiveBack.aggFst_frame";
/// Lens law put-put: a second give-back overrides the first (no accumulation).
pub const GIVEBACK_AGG_PUT_PUT: &str = "RustSem.GiveBack.aggFst_putPut";
/// The give-back of `p.0 += 1`: after the field mutation, reading `p.0` yields
/// `incr(old p.0)` (and, by [`GIVEBACK_AGG_FRAME`], `p.1` is unchanged).
pub const GIVEBACK_AGG_INCR: &str = "RustSem.GiveBack.aggFst_incr";
/// Universe-POLYMORPHIC field-0 pair lens: `fstLensP.{u} {A B : Type u} p a =
/// Prod.mk a p.snd`. Generalizes the give-back of `p.0 = a` (a field SET) to a pair
/// of ANY (same-universe) element types — the lens laws hold for all `A`, `B`, so
/// this ONE lens subsumes the per-element-type aggregate lenses. The general-lens
/// answer to "the inner lens shapes are still per-shape".
pub const GIVEBACK_AGG_FST_LENS_P: &str = "RustSem.GiveBack.fstLensP";
/// Polymorphic put-get: `∀ {A B} p a, (fstLensP p a).fst = a` (proj-ι).
pub const GIVEBACK_AGG_FST_LENS_P_PUTGET: &str = "RustSem.GiveBack.fstLensP_putGet";
/// Polymorphic get-put (round-trip via structure-eta): `∀ {A B} p, fstLensP p p.fst = p`.
pub const GIVEBACK_AGG_FST_LENS_P_GETPUT: &str = "RustSem.GiveBack.fstLensP_getPut";
/// Polymorphic frame: `∀ {A B} p a, (fstLensP p a).snd = p.snd` (proj-ι, sibling untouched).
pub const GIVEBACK_AGG_FST_LENS_P_FRAME: &str = "RustSem.GiveBack.fstLensP_frame";
/// Universe-POLYMORPHIC field-1 pair lens: `sndLensP.{u} {A B : Type u} p b =
/// Prod.mk p.fst b`. The sibling of [`GIVEBACK_AGG_FST_LENS_P`] — the give-back of
/// `p.1 = b` over a pair of ANY element types. Together the two projections form the
/// complete pair lens, generically.
pub const GIVEBACK_AGG_SND_LENS_P: &str = "RustSem.GiveBack.sndLensP";
/// Polymorphic put-get: `∀ {A B} p b, (sndLensP p b).snd = b` (proj-ι).
pub const GIVEBACK_AGG_SND_LENS_P_PUTGET: &str = "RustSem.GiveBack.sndLensP_putGet";
/// Polymorphic get-put (round-trip via structure-eta): `∀ {A B} p, sndLensP p p.snd = p`.
pub const GIVEBACK_AGG_SND_LENS_P_GETPUT: &str = "RustSem.GiveBack.sndLensP_getPut";
/// Polymorphic frame: `∀ {A B} p b, (sndLensP p b).fst = p.fst` (proj-ι, sibling untouched).
pub const GIVEBACK_AGG_SND_LENS_P_FRAME: &str = "RustSem.GiveBack.sndLensP_frame";
/// **The GENERAL n-ary lens answer — lens COMPOSITION preserves put-get.** For any two
/// abstract lenses (`get_o`/`put_o : S↔M`, `get_i`/`put_i : M↔A`) each satisfying their
/// own put-get, the composed lens satisfies put-get:
/// `get_i (get_o (put_o s (put_i (get_o s) a))) = a`. Field-k of an n-ary struct is a
/// composition of `fst`/`snd` lenses down the nested-product spine, so this ONE theorem
/// certifies every field of every arity — the anti-catalog answer to "only 2-tuples".
/// Proof: `Eq.trans` of `congrArg get_i (putGet_o …)` and `putGet_i …`.
pub const GIVEBACK_AGG_LENS_COMPOSE_PUTGET: &str = "RustSem.GiveBack.lensCompose_putGet";
/// **Lens COMPOSITION preserves get-put** (the round-trip half): for composable lenses
/// each satisfying get-put, `put_o s (put_i (get_o s) (get_i (get_o s))) = s`. Proof:
/// `Eq.trans` of `congrArg (put_o s) (getPut_i …)` and `getPut_o …`.
pub const GIVEBACK_AGG_LENS_COMPOSE_GETPUT: &str = "RustSem.GiveBack.lensCompose_getPut";
/// **POLYMORPHIC nested (`p.0.0`) give-back round-trip**, obtained by INSTANTIATING
/// [`GIVEBACK_AGG_LENS_COMPOSE_GETPUT`] at two `fst` lenses: for ANY `A B C : Type u`,
/// `∀ (s : Prod (Prod A B) C), fstLensP s (fstLensP s.fst s.fst.fst) = s`. The deep-field
/// give-back is a *composed* lens, so nested access is general for any types — the payoff of
/// the composition theorem (no bespoke nested proof, no `Nat`-specificity).
pub const GIVEBACK_AGG_NEST_LENS_GETPUT: &str = "RustSem.GiveBack.nestFstLensP_getPut";

// ── Sum-type (enum) give-back (a `&mut` into an `Option<Nat>` payload) ────────
/// Backward function for a `&mut` into a sum-type variant: `optSet o v'` rebuilds
/// the SAME variant with payload `v'` if present, framing the `none` variant
/// (`Option.rec` case analysis).
pub const GIVEBACK_OPT_SET: &str = "RustSem.GiveBack.optSet";
/// Reconstruct-same-variant (the sum-type analog of structure eta, but proved by
/// the recursor — sums have no eta): `optSelf o` rebuilds `o` from its variant.
pub const GIVEBACK_OPT_SELF: &str = "RustSem.GiveBack.optSelf";
/// The give-back of `*x += 1` mapped through the payload: `optIncr (some a) =
/// some (a+1)`, `optIncr none = none` (`Option::map(|x| x+1)`).
pub const GIVEBACK_OPT_INCR: &str = "RustSem.GiveBack.optIncr";
/// Sum-type frame: a give-back on the `none` variant changes nothing.
pub const GIVEBACK_OPT_FRAME_NONE: &str = "RustSem.GiveBack.optSet_frameNone";
/// Sum-type set: a give-back on `some _` overwrites the payload.
pub const GIVEBACK_OPT_SET_SOME: &str = "RustSem.GiveBack.optSet_setSome";
/// Sum-type put-put (proved BY CASE ANALYSIS over the opaque `o` via `Option.rec`).
pub const GIVEBACK_OPT_PUT_PUT: &str = "RustSem.GiveBack.optSet_putPut";
/// Sum-type round-trip (`∀ o, optSelf o = o`; proved by `Option.rec` per variant).
pub const GIVEBACK_OPT_ROUNDTRIP: &str = "RustSem.GiveBack.optSelf_roundTrip";
/// The give-back of `*x += 1` through the `some` variant: `optIncr (some a) =
/// some (a+1)`.
pub const GIVEBACK_OPT_INCR_SOME: &str = "RustSem.GiveBack.optIncr_some";
/// INDUCTIVE BRIDGE: representation function `Option Nat → Prod Bool Nat` (a tagged
/// struct `{isSome, payload}`), the retraction back, and the theorem that the
/// tagged-struct give-back CORRESPONDS to the inductive `optIncr`. Proves the IR-level
/// (tagged-struct) enum give-back faithfully models the source-level `Option.rec`
/// give-back — pure math, no compiler-lowering assumption.
pub const GIVEBACK_OPT_TO_TAGGED: &str = "RustSem.GiveBack.optToTagged";
/// Retraction `Prod Bool Nat → Option Nat` (the tagged struct read back as an Option).
pub const GIVEBACK_OPT_FROM_TAGGED: &str = "RustSem.GiveBack.optFromTagged";
/// The tagged-struct give-back of `Some(x) => *x += 1`: `taggedOptIncr {t, p} =
/// {t, if t then p+1 else p}` (frame the tag, increment the payload on the `some` tag).
pub const GIVEBACK_OPT_TAGGED_INCR: &str = "RustSem.GiveBack.taggedOptIncr";
/// **The bridge theorem**: `∀ o, optFromTagged (taggedOptIncr (optToTagged o)) =
/// optIncr o` — the tagged-struct give-back, viewed as an Option, equals the inductive
/// give-back. Proved by `Option.rec` + `Bool.rec` ι-reduction (per variant, `Eq.refl`).
pub const GIVEBACK_OPT_TAGGED_BRIDGE: &str = "RustSem.GiveBack.optTaggedBridge";
/// `Result`-style TWO-PAYLOAD match: increment the payload in BOTH arms of a `Sum Nat Nat`.
pub const GIVEBACK_SUM_INCR: &str = "RustSem.GiveBack.sumIncr";
/// The backward function for [`GIVEBACK_SUM_INCR`] (decrement in both arms).
pub const GIVEBACK_SUM_INCR_BACK: &str = "RustSem.GiveBack.sumIncrBack";
/// **Two-payload pattern-match give-back**: `∀ (s : Sum Nat Nat), sumIncrBack (sumIncr s) =
/// s` — the give-back of a `&mut Result<T,E>`-style match that mutates BOTH arms, proved by
/// `Sum.rec` case analysis (per-arm `Eq.refl` via `Nat.sub` ι). Generalizes the `Option`
/// give-back (which has a payload-free `None` arm) to a sum with two distinct payloads.
pub const GIVEBACK_SUM_ROUNDTRIP: &str = "RustSem.GiveBack.sumIncr_roundTrip";
/// POLYMORPHIC two-payload map: `sumMap.{u} {A B:Type u} (fa:A→A)(fb:B→B)` over `Sum A B`.
pub const GIVEBACK_SUM_MAP: &str = "RustSem.GiveBack.sumMap";
/// **The GENERAL two-payload pattern-match give-back**: for ANY payload types `A B` and ANY
/// per-arm reversible ops `fa,fb` (with left inverses `fia,fib`), `sumMap fia fib (sumMap fa
/// fb s) = s`. The anti-catalog generalization of [`GIVEBACK_SUM_ROUNDTRIP`] from `Nat` to
/// arbitrary payloads/ops — a `&mut Result<T,E>` match over any `T`,`E` gives back. Proved
/// by `Sum.rec`; each arm rewrites via its inverse hypothesis (`congrArg` on `inl`/`inr`).
pub const GIVEBACK_SUM_MAP_ROUNDTRIP: &str = "RustSem.GiveBack.sumMap_roundTrip";
/// POLYMORPHIC Option payload map: `optMap.{v} {A:Type v} (f:A→A)` over `Option A`.
pub const GIVEBACK_OPT_MAP: &str = "RustSem.GiveBack.optMap";
/// **The GENERAL `Option` match give-back**: for ANY payload type `A` and ANY reversible op
/// `f` (left inverse `finv`), `optMap finv (optMap f o) = o`. The universe-polymorphic
/// generalization of the `Option Nat` give-back — so `&mut Option<T>` for any `T` gives back.
/// Proved by `Option.rec`: the `some` arm rewrites via the inverse hypothesis (`congrArg`
/// `Option.some`), the `none` arm is `Eq.refl`. Completes pattern-match generality with
/// [`GIVEBACK_SUM_MAP_ROUNDTRIP`] (both `Option` and `Sum`/`Result` now polymorphic).
pub const GIVEBACK_OPT_MAP_ROUNDTRIP: &str = "RustSem.GiveBack.optMap_roundTrip";

// ── Recursive give-back (a `&mut` into a `List<Nat>` — the list_nth_mut tier) ─
/// Reconstruct an arbitrarily-deep recursive structure: `listSelf l` rebuilds the
/// whole list from its spine (`List.rec`, structural recursion).
pub const GIVEBACK_LIST_SELF: &str = "RustSem.GiveBack.listSelf";
/// The give-back of `*x += 1` mapped over every element (`l.iter_mut().for_each`).
pub const GIVEBACK_LIST_INCR: &str = "RustSem.GiveBack.listIncr";
/// `listSelf (cons h t) = cons h (listSelf t)` — the recursion unfolds (ι).
pub const GIVEBACK_LIST_SELF_CONS: &str = "RustSem.GiveBack.listSelf_cons";
/// **The recursive round-trip** `∀ l, listSelf l = l` — proved by STRUCTURAL
/// INDUCTION (`List.rec` whose cons minor consumes the recursion hypothesis
/// `ih : listSelf t = t`). This is the load-bearing induction `list_nth_mut`'s
/// give-back soundness rests on, and the capability beyond the (non-recursive)
/// product/sum cases.
pub const GIVEBACK_LIST_ROUNDTRIP: &str = "RustSem.GiveBack.listSelf_roundTrip";
/// `listIncr (cons h t) = cons (h+1) (listIncr t)` — the per-step give-back (ι).
pub const GIVEBACK_LIST_INCR_CONS: &str = "RustSem.GiveBack.listIncr_cons";

// ── Disjoint mutable borrows (the `split_at_mut` separation property) ─────────
/// Backward function for the FIRST of two disjoint `&mut`s into a pair (`&mut p.0`).
pub const GIVEBACK_SPLIT_BACK0: &str = "RustSem.GiveBack.splitBack0";
/// Backward function for the SECOND disjoint `&mut` (`&mut p.1`).
pub const GIVEBACK_SPLIT_BACK1: &str = "RustSem.GiveBack.splitBack1";
/// Non-interference: giving back through borrow 0 leaves what borrow 1 reads (`p.1`).
pub const GIVEBACK_SPLIT_DISJOINT01: &str = "RustSem.GiveBack.split_disjoint01";
/// Non-interference: giving back through borrow 1 leaves what borrow 0 reads (`p.0`).
pub const GIVEBACK_SPLIT_DISJOINT10: &str = "RustSem.GiveBack.split_disjoint10";
/// **The separation law**: the two disjoint give-backs COMMUTE (recombination
/// order is irrelevant) — Rust's aliasing-XOR-mutation made sound.
pub const GIVEBACK_SPLIT_COMMUTE: &str = "RustSem.GiveBack.split_commute";
/// Recombining both disjoint borrows fully determines the pair (`= Prod.mk v0 v1`).
pub const GIVEBACK_SPLIT_COMBINE: &str = "RustSem.GiveBack.split_combine";

// ── Control-flow give-back (the give-back of `if c { *x = v }`) ───────────────
/// Backward function of a CONDITIONAL mutation: `condSet c old v` = `v` if the
/// branch is taken, else the unchanged `old` (`Bool.rec` on the runtime flag).
pub const GIVEBACK_COND_SET: &str = "RustSem.GiveBack.condSet";
/// Branch taken: `condSet true old v = v` (ι).
pub const GIVEBACK_COND_TRUE: &str = "RustSem.GiveBack.condSet_true";
/// Branch NOT taken (frame): `condSet false old v = old` (ι).
pub const GIVEBACK_COND_FALSE: &str = "RustSem.GiveBack.condSet_false";
/// **`∀ c`, by case analysis**: setting the field to its current value is a no-op
/// on EITHER branch — `condSet c old old = old` (`Bool.rec` over the opaque flag).
pub const GIVEBACK_COND_SELF: &str = "RustSem.GiveBack.condSet_self";
/// Prod-typed conditional give-back combinator, for a conditional mutation whose
/// PLACE is a pair — e.g. `if c { p.0 += 1 }` over `&mut (Nat, Nat)`. `condSetPair
/// c old v = Bool.rec old v c` over `Prod Nat Nat` (false→old, true→v). Same universe
/// levels as [`GIVEBACK_COND_SET`] (`Prod Nat Nat : Sort 1`), so this is give-back
/// COMPOSITION — the conditional (T-cond) over the aggregate (H3) place — in ONE env.
pub const GIVEBACK_COND_SET_PAIR: &str = "RustSem.GiveBack.condSetPair";
/// Branch taken (pair): `condSetPair true old v = v` (ι).
pub const GIVEBACK_COND_PAIR_TRUE: &str = "RustSem.GiveBack.condSetPair_true";
/// Branch framed (pair): `condSetPair false old v = old` (ι).
pub const GIVEBACK_COND_PAIR_FALSE: &str = "RustSem.GiveBack.condSetPair_false";
/// Universe-POLYMORPHIC conditional give-back combinator — ONE law for ANY place
/// type α (scalar, pair, nested, tagged-enum, …), so the conditional composes with
/// any inner give-back WITHOUT a per-type combinator. `condSetP.{u} {α : Type u} c
/// old v = Bool.rec (λ _ => α) old v c`. Subsumes [`GIVEBACK_COND_SET`] (α := Nat)
/// and [`GIVEBACK_COND_SET_PAIR`] (α := Prod Nat Nat) — the anti-catalog primitive.
pub const GIVEBACK_COND_SET_POLY: &str = "RustSem.GiveBack.condSetP";
/// Branch taken (polymorphic): `∀ {α} old v, condSetP true old v = v` (ι).
pub const GIVEBACK_COND_POLY_TRUE: &str = "RustSem.GiveBack.condSetP_true";
/// Branch framed (polymorphic): `∀ {α} old v, condSetP false old v = old` (ι).
pub const GIVEBACK_COND_POLY_FALSE: &str = "RustSem.GiveBack.condSetP_false";

// ── Nested give-back (a `&mut` into a NESTED field — `&mut p.0.0`) ────────────
/// Forward of a borrow two levels deep: `nestFwd p = (p.fst).fst`.
pub const GIVEBACK_NEST_FWD: &str = "RustSem.GiveBack.nestFwd";
/// Backward of a nested borrow: rebuild BOTH levels — inner pair with the deep
/// field updated, then the outer pair — framing both siblings.
pub const GIVEBACK_NEST_BACK: &str = "RustSem.GiveBack.nestBack";
/// Nested put-get: reading the deep field back yields what was given back (ι×2).
pub const GIVEBACK_NEST_PUT_GET: &str = "RustSem.GiveBack.nest_putGet";
/// **Nested round-trip**: `nestBack p (nestFwd p) = p` — requires structure-eta to
/// fire at BOTH nesting levels.
pub const GIVEBACK_NEST_GET_PUT: &str = "RustSem.GiveBack.nest_getPut";
/// Frame the INNER sibling (`p.0.1` untouched by a `&mut p.0.0`).
pub const GIVEBACK_NEST_FRAME_INNER: &str = "RustSem.GiveBack.nest_frameInner";
/// Frame the OUTER sibling (`p.1` untouched by a `&mut p.0.0`).
pub const GIVEBACK_NEST_FRAME_OUTER: &str = "RustSem.GiveBack.nest_frameOuter";
/// The give-back of `p.0.0 += 1`: reading the deep field back yields `incr(old)`
/// (`nestFwd (nestBack p (nestFwd p + 1)) = nestFwd p + 1`), with both siblings
/// framed by [`GIVEBACK_NEST_FRAME_INNER`]/[`GIVEBACK_NEST_FRAME_OUTER`].
pub const GIVEBACK_NEST_INCR: &str = "RustSem.GiveBack.nest_incr";

// ── Loop give-back (`for x in &mut l { *x += 1 }` — Aeneas loop backward fns) ─
/// The loop FORWARD: `map (+1)` over the whole list (the loop body's effect).
pub const GIVEBACK_LOOP_FWD: &str = "RustSem.GiveBack.loopFwd";
/// The loop BACKWARD function: `map pred` — the give-back that undoes the loop.
pub const GIVEBACK_LOOP_BACK: &str = "RustSem.GiveBack.loopBack";
/// `loopFwd (cons h t) = cons (h+1) (loopFwd t)` — one loop iteration (ι).
pub const GIVEBACK_LOOP_FWD_CONS: &str = "RustSem.GiveBack.loopFwd_cons";
/// **The loop round-trip** `∀ l, loopBack (loopFwd l) = l` — the loop's backward
/// function inverts its forward over the ENTIRE list, proved by STRUCTURAL
/// INDUCTION (per element `pred (h+1) = h`, lifted through the spine). Aeneas's
/// signature loop-give-back property.
pub const GIVEBACK_LOOP_ROUNDTRIP: &str = "RustSem.GiveBack.loop_roundTrip";
/// GENERIC list map by an arbitrary element function: `listMap g l` maps `g` over `l`.
pub const GIVEBACK_LOOP_MAP: &str = "RustSem.GiveBack.listMap";
/// **The GENERAL loop give-back law** (arbitrary-body loop, not just `+1`): for ANY
/// element function `f` with a left inverse `finv` (`∀ x, finv (f x) = x`), the map
/// round-trips — `∀ l, listMap finv (listMap f l) = l`. Proved by `List.rec` structural
/// induction; the cons case rewrites the head via the inverse hypothesis and the tail
/// via the IH (`Eq.trans` of two `congrArg`s). Subsumes `loop_roundTrip` (`f=+1`,
/// `finv=pred`) — the anti-catalog answer for loops over any reversible element op.
pub const GIVEBACK_LOOP_MAP_ROUNDTRIP: &str = "RustSem.GiveBack.listMap_roundTrip";
/// TYPE-POLYMORPHIC generic list map: `listMapT.{u} {A : Type u} (g : A → A)` over `List A`.
pub const GIVEBACK_LOOP_MAP_T: &str = "RustSem.GiveBack.listMapT";
/// **The FULLY GENERAL loop give-back law**: for ANY element type `A` and ANY element
/// function `f : A → A` with a left inverse `finv`, `listMapT finv (listMapT f l) = l`.
/// The universe-polymorphic generalization of [`GIVEBACK_LOOP_MAP_ROUNDTRIP`] from
/// `Nat → Nat` to arbitrary `A` — so a loop `for x in &mut l { *x = f x }` over a sequence
/// of ANY type (pairs, enums, …) gives back, not just integer loops. Same `List.rec` +
/// `Eq.trans`-of-`congrArg` proof, abstracted over the element type.
pub const GIVEBACK_LOOP_MAP_T_ROUNDTRIP: &str = "RustSem.GiveBack.listMapT_roundTrip";
/// `not_not : ∀ b, Bool.not (Bool.not b) = b` — the Bool.not involution (Bool.rec, ι).
pub const GIVEBACK_LOOP_NOT_NOT: &str = "RustSem.GiveBack.not_not";
/// A CONCRETE non-`+k`, non-`Nat` loop give-back: the boolean-flip loop
/// `for b in &mut l { *b = !*b }` round-trips (`∀ l:List Bool, listMapT not (listMapT not
/// l) = l`), obtained by INSTANTIATING [`GIVEBACK_LOOP_MAP_T_ROUNDTRIP`] at `A=Bool`,
/// `f=finv=Bool.not` with `not_not` — zero new induction. Proof that the general loop law
/// delivers new element ops (and element types) for the price of one inverse lemma.
pub const GIVEBACK_LOOP_BOOLNOT_ROUNDTRIP: &str = "RustSem.GiveBack.boolNotLoop_roundTrip";
/// A loop over a sequence of PAIRS incrementing field 0: `for p in &mut l { p.0 += 1 }`
/// round-trips (`∀ l:List (Prod Nat Nat), listMapT dec (listMapT inc l) = l`), where
/// `inc p = (p.0+1, p.1)` and `dec p = (p.0-1, p.1)`. The THIRD recognized invertible
/// element op — over a STRUCTURED element type (a product) — obtained by instantiating
/// [`GIVEBACK_LOOP_MAP_T_ROUNDTRIP`] at `A = Prod Nat Nat`; the per-element inverse is
/// `Eq.refl` (Nat.sub ι + Prod structure-eta). Loop over a `Vec<Struct>` mutating a field.
pub const GIVEBACK_LOOP_PAIRINCR_ROUNDTRIP: &str = "RustSem.GiveBack.pairIncrLoop_roundTrip";

// ── Generic give-back (`fn f<T>(x: &mut T)` — the value-polymorphic law, instanced) ─
/// The generic give-back memory law instantiated at `Nat` (a scalar `T`).
pub const GIVEBACK_GEN_NAT: &str = "RustSem.GiveBack.genericRaw_Nat";
/// Instantiated at `Bool` (a different scalar `T`).
pub const GIVEBACK_GEN_BOOL: &str = "RustSem.GiveBack.genericRaw_Bool";
/// Instantiated at `Prod Nat Nat` (a STRUCT `T` — `fn f<T>` works for aggregates).
pub const GIVEBACK_GEN_PROD: &str = "RustSem.GiveBack.genericRaw_Prod";

// ── Closure give-back (an `FnMut` reconstructs its captured environment) ──────
/// One call of an `FnMut` over its captured env (`mut` capture `+= arg`, `ref`
/// capture framed): `closureCall e y = Prod.mk (e.fst + y) e.snd`.
pub const GIVEBACK_CLO_CALL: &str = "RustSem.GiveBack.closureCall";
/// The call's effect on the mutated capture: `(closureCall e y).fst = e.fst + y` (ι).
pub const GIVEBACK_CLO_CALL_EFFECT: &str = "RustSem.GiveBack.closure_callEffect";
/// Frame: a by-ref capture (`e.snd`) is untouched by the call.
pub const GIVEBACK_CLO_FRAME: &str = "RustSem.GiveBack.closure_frameCapture";
/// **No-op call**: `∀ e, closureCall e 0 = e` — calling with the identity arg
/// reconstructs the whole env unchanged (`Nat.add e.fst 0 = e.fst` by ι, then
/// structure-eta on the env).
pub const GIVEBACK_CLO_NOOP: &str = "RustSem.GiveBack.closure_noopCall";

// ── Trait give-back (dyn dispatch through a vtable — trait objects) ───────────
/// Dynamic dispatch: call the method stored in a trait object's vtable
/// (`vtbl = (method, data)`): `vtblDispatch v x = (v.fst) x`.
pub const GIVEBACK_TRAIT_DISPATCH: &str = "RustSem.GiveBack.vtblDispatch";
/// **The dyn-dispatch fact**: `∀ f d x, vtblDispatch (mk f d) x = f x` — the call
/// resolves to whatever method the vtable carries (the call site is impl-agnostic).
pub const GIVEBACK_TRAIT_RESOLVES: &str = "RustSem.GiveBack.dispatch_resolves";
/// Concrete identity impl: `dispatch (mk (λz.z) d) x = x` (proj-ι + β).
pub const GIVEBACK_TRAIT_ID: &str = "RustSem.GiveBack.dispatch_idImpl";
/// Concrete incrementing impl: `dispatch (mk (λz.z+1) d) x = x + 1` (proj-ι + β).
pub const GIVEBACK_TRAIT_INCR: &str = "RustSem.GiveBack.dispatch_incrImpl";
/// An ASSOCIATED TYPE resolved by an impl: `<NatContainer as Container>::Item = Nat`.
pub const GIVEBACK_ASSOC_ITEM: &str = "RustSem.GiveBack.assocItem";
/// The give-back of `&mut Self::Item` incrementing, DEFINED at the associated type.
pub const GIVEBACK_ASSOC_INCR_BACK: &str = "RustSem.GiveBack.assocIncrBack";
/// **Associated-type give-back**: `∀ (v : Self::Item), assocIncrBack v = v + 1` — the
/// give-back through an associated-type-typed `&mut` resolves (definitionally, via the
/// impl's `Item = Nat`) to the give-back at the concrete resolved type. Associated types
/// are a type-level indirection that does NOT obstruct give-back. Axiom-clean (Eq.refl).
pub const GIVEBACK_ASSOC_INCR: &str = "RustSem.GiveBack.assoc_incr_roundTrip";

// ── Vec/std-collection give-back (push / pop — a `Vec` as a stack) ────────────
/// `Vec::push` (front): `vecPush x v = cons x v`.
pub const GIVEBACK_VEC_PUSH: &str = "RustSem.GiveBack.vecPush";
/// `Vec` front element (`vecHead`, `0` on empty).
pub const GIVEBACK_VEC_HEAD: &str = "RustSem.GiveBack.vecHead";
/// `Vec` rest after the front (`vecTail`).
pub const GIVEBACK_VEC_TAIL: &str = "RustSem.GiveBack.vecTail";
/// **push/pop round-trip (element)**: `∀ x v, vecHead (vecPush x v) = x` — popping
/// returns exactly what was pushed (ι).
pub const GIVEBACK_VEC_PUSH_POP_HEAD: &str = "RustSem.GiveBack.vec_pushPopHead";
/// **push/pop round-trip (rest)**: `∀ x v, vecTail (vecPush x v) = v` — the rest of
/// the `Vec` is exactly what was there before the push (ι).
pub const GIVEBACK_VEC_PUSH_POP_TAIL: &str = "RustSem.GiveBack.vec_pushPopTail";

// ── HashMap give-back (a `HashMap<Nat,Nat>` with presence/absence) ───────────
/// `HashMap::get` over a partial map `Nat → Option Nat` (`none` = absent).
pub const GIVEBACK_MAP_GET: &str = "RustSem.GiveBack.mapGet";
/// `HashMap::insert`: `mapInsert m k v` maps `k ↦ some v`, frames every other key.
pub const GIVEBACK_MAP_INSERT: &str = "RustSem.GiveBack.mapInsert";
/// `HashMap::remove`: `mapRemove m k` maps `k ↦ none`, frames every other key.
pub const GIVEBACK_MAP_REMOVE: &str = "RustSem.GiveBack.mapRemove";
/// `get` after `insert` at the same key: `mapGet (mapInsert m k v) k = some v`.
pub const GIVEBACK_MAP_INSERT_GET: &str = "RustSem.GiveBack.map_insertGet";
/// **`get` after `remove`**: `mapGet (mapRemove m k) k = none` — the key is gone
/// (the presence/absence law a HashMap must satisfy).
pub const GIVEBACK_MAP_REMOVE_GET: &str = "RustSem.GiveBack.map_removeGet";

// ── Operational step + bisimulation (T-step, first increment) ────────────────
/// A reflected small-step `step` over the store, indexed by an OPERATION (an
/// `Option Nat`: `some v` = "write v", `none` = "incr"). `gbStep s a op` runs one
/// memory operation at address `a` (`Option.rec` dispatch on the op).
pub const GIVEBACK_STEP: &str = "RustSem.GiveBack.gbStep";
/// **Bisimulation (write)**: after a write step, reading the address yields the
/// written value — `gbLookup (gbStep s a (some v)) a = v`.
pub const GIVEBACK_STEP_WRITE: &str = "RustSem.GiveBack.step_writeReadsBack";
/// **Bisimulation (incr)**: after an incr step, reading the address yields the
/// give-back `incrBack (old)` — `gbLookup (gbStep s a none) a = incrBack (gbLookup s a)`.
pub const GIVEBACK_STEP_INCR: &str = "RustSem.GiveBack.step_incrReadsBack";
/// **Multi-step trace bisimulation**: last-write-wins across a TWO-step trace —
/// `gbLookup (gbStep (gbStep s a (some v1)) a (some v2)) a = v2`.
pub const GIVEBACK_STEP_SEQ: &str = "RustSem.GiveBack.step_seqWriteLastWins";
/// **§3.5 disjoint-Place frame (step level)**: a write step does NOT affect any
/// other address — `a' ≠ a → gbLookup (gbStep s a (some v)) a' = gbLookup s a'`.
/// (cfg-gated: needs `Nat.beq_eq_false_of_ne`, like the store frame law.)
pub const GIVEBACK_STEP_FRAME: &str = "RustSem.GiveBack.step_frameDisjoint";
/// **§3.5 memory-level GIVE-BACK ROUND-TRIP**: the operational statement that the give-back
/// recovers the original store value at the mutated address. After incrementing address `a`
/// (a `none` step) and then giving back — writing the saved original `gbLookup s a` (a
/// `some` step) — reading `a` yields the original: `gbLookup (gbStep (gbStep s a none) a
/// (some (gbLookup s a))) a = gbLookup s a`. This is Aeneas's give-back guarantee stated at
/// the OPERATIONAL memory-step level (the backward function closes over the saved context),
/// grounding the pure give-back algebra in the value-at-address semantics.
pub const GIVEBACK_STEP_ROUNDTRIP: &str = "RustSem.GiveBack.step_incrGiveBackRoundTrip";

impl Environment {
    /// Build the in-process give-back refinement anchor: admit the identity
    /// backward function and its round-trip law as an axiom-clean
    /// `Declaration::Theorem`. See module docs.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`) or either give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);

        // backId : Nat → Nat := fun v => v   (the identity backward function)
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_BACK_ID),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), nat.clone()),
            value: Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
            is_reducible: true,
        })?;

        // backId_roundTrips : ∀ v : Nat, Eq Nat (backId v) v := fun v => Eq.refl Nat v
        // Well-typed because the kernel reduces `backId v` to `v` (δ + β).
        let one = Level::succ(Level::zero());
        let back_id = Expr::const_(Name::from_string(GIVEBACK_BACK_ID), vec![]);
        let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

        let lhs = Expr::app(back_id, Expr::bvar(0)); // backId v
        let eq_body = Expr::apps(eq, [nat.clone(), lhs, Expr::bvar(0)]); // Eq Nat (backId v) v
        let stmt = Expr::pi(BinderInfo::Default, nat.clone(), eq_body);

        let refl_app = Expr::apps(eq_refl, [nat.clone(), Expr::bvar(0)]); // Eq.refl Nat v
        let proof = Expr::lam(BinderInfo::Default, nat, refl_app);

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_BACK_ID_ROUNDTRIPS),
            level_params: vec![],
            type_: stmt,
            value: proof,
        })?;

        // ── Universe-POLYMORPHIC identity give-back: an UNTOUCHED `&mut` of ANY type
        //    gives back its input unchanged. `backIdP.{u} {α:Type u} v = v`; the
        //    round-trip holds for every α (α : Type u = Sort (u+1) ⇒ Eq.{u+1}).
        let up_name = Name::from_string("u");
        let up_lvl = Level::param(up_name.clone());
        let type_up = Expr::sort(Level::succ(up_lvl.clone()));
        let eq_up = Expr::const_(Name::from_string("Eq"), vec![Level::succ(up_lvl.clone())]);
        let eq_refl_up = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(up_lvl.clone())],
        );
        let back_id_p =
            |lvl: Level| Expr::const_(Name::from_string(GIVEBACK_BACK_ID_POLY), vec![lvl]);

        // backIdP : {α : Type u} → α → α := λ {α} v => v
        let bidp_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_up.clone());
            let e = Expr::arrow(a.clone(), a.clone());
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_up.clone(), e))
        };
        let bidp_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_up.clone());
            let (v_id, v) = b.fresh_local(a.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, a.clone(), v);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_up.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_BACK_ID_POLY),
            level_params: vec![up_name.clone()],
            type_: bidp_type,
            value: bidp_val,
            is_reducible: true,
        })?;

        // backIdP_roundTrips : {α : Type u} → ∀ v, backIdP v = v
        let bidp_rt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_up.clone());
            let (v_id, v) = b.fresh_local(a.clone());
            let lhs = Expr::apps(back_id_p(up_lvl.clone()), [a.clone(), v.clone()]);
            let concl = Expr::apps(eq_up.clone(), [a.clone(), lhs, v.clone()]);
            let e = b.mk_pi(v_id, BinderInfo::Default, a.clone(), concl);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_up.clone(), e))
        };
        let bidp_rt_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_up.clone());
            let (v_id, v) = b.fresh_local(a.clone());
            let refl = Expr::apps(eq_refl_up.clone(), [a.clone(), v.clone()]);
            let e = b.mk_lam(v_id, BinderInfo::Default, a.clone(), refl);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_up.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_BACK_ID_POLY_ROUNDTRIPS),
            level_params: vec![up_name],
            type_: bidp_rt_type,
            value: bidp_rt_val,
        })?;

        // ── incr: the give-back of a `*x += 1` mutation ──────────────────────
        // The backward function for `*x += 1` is `incrBack v = v + 1`, and the
        // give-back lens algebra is its composition laws. Unlike the identity
        // round-trip, these are proved by REAL symbolic ι-reduction of the
        // structural `Nat.add` recursor (both sides whnf to `Nat.succ (… v)`),
        // not arithmetic on closed literals — the give-back of a real mutation.
        let nat = Expr::const_(Name::from_string("Nat"), vec![]); // re-bind (backId proof moved it)
        let one_lvl = Level::succ(Level::zero());
        let eq2 = Expr::const_(Name::from_string("Eq"), vec![one_lvl.clone()]);
        let eq_refl2 = Expr::const_(Name::from_string("Eq.refl"), vec![one_lvl]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let lit = |n: u32| {
            let mut e = nat_zero.clone();
            for _ in 0..n {
                e = Expr::app(nat_succ.clone(), e);
            }
            e
        };

        // incrBack : Nat → Nat := fun v => Nat.add v 1
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_INCR_BACK),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), nat.clone()),
            value: Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::apps(nat_add.clone(), [Expr::bvar(0), lit(1)]),
            ),
            is_reducible: true,
        })?;
        let incr_back = Expr::const_(Name::from_string(GIVEBACK_INCR_BACK), vec![]);

        // Build `∀ v, Eq Nat (incrBack^k v) (Nat.add v k)` proved by Eq.refl.
        let mut compose_law = |name: &str, k: u32| -> Result<(), EnvError> {
            let mut lhs = Expr::bvar(0);
            for _ in 0..k {
                lhs = Expr::app(incr_back.clone(), lhs);
            }
            let rhs = Expr::apps(nat_add.clone(), [Expr::bvar(0), lit(k)]);
            let stmt = Expr::pi(
                BinderInfo::Default,
                nat.clone(),
                Expr::apps(eq2.clone(), [nat.clone(), lhs, rhs.clone()]),
            );
            let proof = Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::apps(eq_refl2.clone(), [nat.clone(), rhs]),
            );
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_: stmt,
                value: proof,
            })
        };
        // incrBack_step : ∀ v, incrBack v = v + 1   (the single-step give-back of `*x += 1`)
        compose_law(GIVEBACK_INCR_STEP, 1)?;
        // incrBack_composes : ∀ v, incrBack (incrBack v) = v + 2
        compose_law(GIVEBACK_INCR_COMPOSES, 2)?;
        // incrBack_thrice : ∀ v, incrBack (incrBack (incrBack v)) = v + 3
        compose_law(GIVEBACK_INCR_THRICE, 3)?;

        // ── addKBack: the give-back of a CONSTANT increment `*x += k` for ANY k.
        //    ONE parameterized law instead of a per-constant family (subsumes
        //    incrBack_step at k = 1). addKBack k v = Nat.add v k, so the step law is
        //    Eq.refl (δ + β). Generalizes the scalar-incr shape from `+1` to `+k`.
        // addKBack : Nat → Nat → Nat := λ k v => Nat.add v k
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_ADD_K_BACK),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
            value: Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::apps(nat_add.clone(), [Expr::bvar(0), Expr::bvar(1)]),
                ),
            ),
            is_reducible: true,
        })?;
        let add_k_back = Expr::const_(Name::from_string(GIVEBACK_ADD_K_BACK), vec![]);
        // addKBack_step : ∀ k v, addKBack k v = Nat.add v k
        let addk_stmt = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::pi(
                BinderInfo::Default,
                nat.clone(),
                Expr::apps(
                    eq2.clone(),
                    [
                        nat.clone(),
                        Expr::apps(add_k_back.clone(), [Expr::bvar(1), Expr::bvar(0)]),
                        Expr::apps(nat_add.clone(), [Expr::bvar(0), Expr::bvar(1)]),
                    ],
                ),
            ),
        );
        let addk_proof = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::apps(
                    eq_refl2.clone(),
                    [
                        nat.clone(),
                        Expr::apps(nat_add.clone(), [Expr::bvar(0), Expr::bvar(1)]),
                    ],
                ),
            ),
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_ADD_K_STEP),
            level_params: vec![],
            type_: addk_stmt,
            value: addk_proof,
        })?;

        // The genuinely-operational memory tier: a real store + read-after-write
        // + frame + the incr give-back-over-store law.
        self.declare_giveback_store()?;

        Ok(())
    }

    /// Build the **`u32` wraparound** give-back anchor — the faithful-to-Rust
    /// answer to "incr is over `Nat`, not `u32`". Defines a real wrapping add over
    /// the `UInt32` REPRESENTATION (`UInt32.mk`/`.val` + `Nat.mod 2³²`, all
    /// non-axioms) and proves the give-back backward function genuinely WRAPS:
    /// `incrBackU32 (u32::MAX) = 0` — true over `u32 mod 2³²`, FALSE over `Nat`.
    /// Proved by kernel reduction (`Nat.add` then `Nat.mod` on the literals).
    ///
    /// Isolated in its own anchor: it pulls `Fin`/`UInt32` (whose kernel setup
    /// carries a few domain axioms) into THIS env only, keeping the main
    /// [`Environment::init_giveback_refinement`] anchor axiom-clean. The wraparound
    /// theorem's OWN axiom closure is clean (it uses only constructors/defs:
    /// `UInt32.mk`/`.val`, `Nat.add`/`Nat.mod`, `Eq.refl`), which is what the
    /// per-theorem CleanCic re-check verifies.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite or a declaration fails to admit.
    pub fn init_giveback_u32_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_fin()?; // UInt32.toFin references Fin
        self.init_uint32()?;

        let u32t = Expr::const_(Name::from_string("UInt32"), vec![]);
        // LEAN 4.8.0 CARRIER: `UInt32.mk : Fin 2^32 → UInt32`,
        // `UInt32.val : UInt32 → Fin 2^32`. Construct via `UInt32.ofNat` (which
        // wraps `Fin.ofNat`, taking `n % 2^32`) and project the underlying `Nat`
        // via `UInt32.toNat` — both carrier-correct reducible defs.
        let u32_ofnat = Expr::const_(Name::from_string("UInt32.ofNat"), vec![]);
        let u32_tonat = Expr::const_(Name::from_string("UInt32.toNat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_mod = Expr::const_(Name::from_string("Nat.mod"), vec![]);
        let mk_u32 = |n: u64| Expr::app(u32_ofnat.clone(), Expr::nat_lit(n));
        let modulus = Expr::nat_lit(4_294_967_296); // 2^32

        // u32Add a b := UInt32.ofNat (Nat.mod (Nat.add (UInt32.toNat a) (UInt32.toNat b)) 2^32)
        // — the faithful wrapping add, defined over the representation (no axiom).
        let u32add_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(u32t.clone());
            let (bb_id, bb) = b.fresh_local(u32t.clone());
            let sum = Expr::apps(
                nat_add.clone(),
                [
                    Expr::app(u32_tonat.clone(), a.clone()),
                    Expr::app(u32_tonat.clone(), bb.clone()),
                ],
            );
            let wrapped = Expr::apps(nat_mod.clone(), [sum, modulus.clone()]);
            let body = Expr::app(u32_ofnat.clone(), wrapped);
            let e = b.mk_lam(bb_id, BinderInfo::Default, u32t.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, u32t.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_U32_ADD),
            level_params: vec![],
            type_: Expr::arrow(u32t.clone(), Expr::arrow(u32t.clone(), u32t.clone())),
            value: u32add_val,
            is_reducible: true,
        })?;
        let u32_add = Expr::const_(Name::from_string(GIVEBACK_U32_ADD), vec![]);

        // incrBackU32 v := u32Add v (UInt32.mk 1)   (the give-back of `*x += 1` over u32)
        let incrb_val = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(u32t.clone());
            let body = Expr::apps(u32_add.clone(), [v.clone(), mk_u32(1)]);
            let e = b.mk_lam(v_id, BinderInfo::Default, u32t.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_INCR_BACK_U32),
            level_params: vec![],
            type_: Expr::arrow(u32t.clone(), u32t.clone()),
            value: incrb_val,
            is_reducible: true,
        })?;
        let incr_back_u32 = Expr::const_(Name::from_string(GIVEBACK_INCR_BACK_U32), vec![]);

        // incrBackU32_wraps : incrBackU32 (UInt32.mk 4294967295) = UInt32.mk 0
        //   by Eq.refl — the kernel reduces u32Add MAX 1 = mk (Nat.mod (MAX+1) 2^32)
        //   = mk (Nat.mod 2^32 2^32) = mk 0. GENUINE u32 overflow (false over Nat).
        let one_lvl = Level::succ(Level::zero());
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one_lvl.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one_lvl]);
        let lhs = Expr::app(incr_back_u32.clone(), mk_u32(4_294_967_295)); // u32::MAX
        let rhs = mk_u32(0);
        let stmt = Expr::apps(eqc.clone(), [u32t.clone(), lhs, rhs.clone()]);
        let proof = Expr::apps(eq_refl.clone(), [u32t.clone(), rhs]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_INCR_U32_WRAPS),
            level_params: vec![],
            type_: stmt,
            value: proof,
        })?;

        Ok(())
    }

    /// Build the **aggregate give-back** anchor — the genuine Aeneas backward
    /// function for a `&mut` into a FIELD of an aggregate (`fn f(p: &mut (u32,u32))
    /// -> &mut _ { &mut p.0 }`). Beyond the scalar `+1` lens: the backward function
    /// `aggFstBack p v' = Prod.mk v' p.snd` literally RECONSTRUCTS the whole pair,
    /// updating field 0 and FRAMING field 1. Proves the four van-Laarhoven lens
    /// laws over `Prod Nat Nat`, all axiom-clean by `Eq.refl` (the kernel discharges
    /// them by δ + projection-ι + **structure eta**):
    ///
    ///   * put-get  `aggFstFwd (aggFstBack p v') = v'`
    ///   * get-put  `aggFstBack p (aggFstFwd p) = p`   (round-trip; needs struct-eta)
    ///   * frame    `(aggFstBack p v').snd = p.snd`     (sibling field untouched)
    ///   * put-put  `aggFstBack (aggFstBack p v1) v2 = aggFstBack p v2`
    ///
    /// plus the composed give-back of `p.0 += 1`
    /// (`aggFstFwd (aggFstBack p (incr (aggFstFwd p))) = incr (aggFstFwd p)`).
    /// get-put is the law a skeptic checks first: it is true ONLY because the
    /// backward function reconstructs the entire aggregate (including the framed
    /// sibling) and the kernel's structure-eta closes the round-trip.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Prod`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_aggregate_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_prod()?; // Prod, Prod.mk, Prod.fst, Prod.snd (proj-based, struct-eta)

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Level::zero();
        // Nat : Type 0 = Sort 1, so `Prod Nat Nat` is instantiated at u=v=0 and
        // both Nat- and (Prod Nat Nat)-equalities are at Sort level 1.
        let prod_lv = vec![zero.clone(), zero.clone()];
        let one = Level::succ(Level::zero());
        let pair_t = Expr::apps(
            Expr::const_(Name::from_string("Prod"), prod_lv.clone()),
            [nat.clone(), nat.clone()],
        );
        let prod_mk = Expr::const_(Name::from_string("Prod.mk"), prod_lv.clone());
        let prod_fst = Expr::const_(Name::from_string("Prod.fst"), prod_lv.clone());
        let prod_snd = Expr::const_(Name::from_string("Prod.snd"), prod_lv);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

        // Prod is parametric with IMPLICIT {α}{β}, so the type args are positional
        // application arguments at the kernel `Expr` level.
        let mk = |a: &Expr, b: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [nat.clone(), nat.clone(), a.clone(), b.clone()],
            )
        };
        let fst = |p: &Expr| Expr::apps(prod_fst.clone(), [nat.clone(), nat.clone(), p.clone()]);
        let snd = |p: &Expr| Expr::apps(prod_snd.clone(), [nat.clone(), nat.clone(), p.clone()]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);
        let eq_pair = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [pair_t.clone(), l, r]);
        let refl_nat = |x: Expr| Expr::apps(eq_refl.clone(), [nat.clone(), x]);
        let refl_pair = |x: Expr| Expr::apps(eq_refl.clone(), [pair_t.clone(), x]);

        // aggFstFwd : Prod Nat Nat → Nat := λ p => p.fst
        let fwd_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let body = fst(&p);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_AGG_FST_FWD),
            level_params: vec![],
            type_: Expr::arrow(pair_t.clone(), nat.clone()),
            value: fwd_val,
            is_reducible: true,
        })?;
        let agg_fwd = Expr::const_(Name::from_string(GIVEBACK_AGG_FST_FWD), vec![]);

        // aggFstBack : Prod Nat Nat → Nat → Prod Nat Nat := λ p v => Prod.mk v p.snd
        let back_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let body = mk(&v, &snd(&p));
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_AGG_FST_BACK),
            level_params: vec![],
            type_: Expr::arrow(pair_t.clone(), Expr::arrow(nat.clone(), pair_t.clone())),
            value: back_val,
            is_reducible: true,
        })?;
        let agg_back = Expr::const_(Name::from_string(GIVEBACK_AGG_FST_BACK), vec![]);
        let fwd = |p: &Expr| Expr::app(agg_fwd.clone(), p.clone());
        let back = |p: &Expr, v: &Expr| Expr::apps(agg_back.clone(), [p.clone(), v.clone()]);

        // put-get : ∀ p v, aggFstFwd (aggFstBack p v) = v   (by δ + proj-ι)
        let put_get_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(fwd(&back(&p, &v)), v.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let put_get_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), refl_nat(v));
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_PUT_GET),
            level_params: vec![],
            type_: put_get_type,
            value: put_get_val,
        })?;

        // get-put : ∀ p, aggFstBack p (aggFstFwd p) = p   (round-trip; structure-eta)
        let get_put_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let concl = eq_pair(back(&p, &fwd(&p)), p.clone());
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), concl))
        };
        let get_put_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), refl_pair(p)))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_GET_PUT),
            level_params: vec![],
            type_: get_put_type,
            value: get_put_val,
        })?;

        // frame : ∀ p v, (aggFstBack p v).snd = p.snd   (sibling field untouched)
        let frame_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(snd(&back(&p, &v)), snd(&p));
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let frame_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let body = refl_nat(snd(&p));
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_FRAME),
            level_params: vec![],
            type_: frame_type,
            value: frame_val,
        })?;

        // put-put : ∀ p v1 v2, aggFstBack (aggFstBack p v1) v2 = aggFstBack p v2
        let put_put_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let (v2_id, v2) = b.fresh_local(nat.clone());
            let concl = eq_pair(back(&back(&p, &v1), &v2), back(&p, &v2));
            let e = b.mk_pi(v2_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(v1_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let put_put_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v1_id, _v1) = b.fresh_local(nat.clone());
            let (v2_id, v2) = b.fresh_local(nat.clone());
            let body = refl_pair(back(&p, &v2));
            let e = b.mk_lam(v2_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(v1_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_PUT_PUT),
            level_params: vec![],
            type_: put_put_type,
            value: put_put_val,
        })?;

        // incr : ∀ p, aggFstFwd (aggFstBack p (aggFstFwd p + 1)) = aggFstFwd p + 1
        // The give-back of `p.0 += 1`: read-back of the mutated field is incr(old);
        // by `frame`, p.1 is untouched. (Nat.add stays symbolic — put-get closes it.)
        let one_lit = Expr::nat_lit(1);
        let incr = |p: &Expr| Expr::apps(nat_add.clone(), [fwd(p), one_lit.clone()]);
        let incr_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let concl = eq_nat(fwd(&back(&p, &incr(&p))), incr(&p));
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), concl))
        };
        let incr_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            b.finish(b.mk_lam(
                p_id,
                BinderInfo::Default,
                pair_t.clone(),
                refl_nat(incr(&p)),
            ))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_INCR),
            level_params: vec![],
            type_: incr_type,
            value: incr_val,
        })?;

        // ── Universe-POLYMORPHIC field-0 pair lens: the general-lens generalization of
        //    the aggregate give-back. `fstLensP.{u} {A B : Type u} p a = Prod.mk a p.snd`
        //    with the lens laws holding for ANY element types A, B — so ONE lens
        //    subsumes the per-element-type aggregate lenses, and certifies the field-SET
        //    give-back `p.0 = a` over a pair of any (same-universe) types. A, B, and
        //    Prod A B are all Type u = Sort (u+1), so every Eq is Eq.{u+1}.
        let up = Name::from_string("u");
        let up_lvl = Level::param(up.clone());
        let type_u = Expr::sort(Level::succ(up_lvl.clone()));
        let plv = vec![up_lvl.clone(), up_lvl.clone()];
        let prodp = Expr::const_(Name::from_string("Prod"), plv.clone());
        let prodp_mk = Expr::const_(Name::from_string("Prod.mk"), plv.clone());
        let prodp_fst = Expr::const_(Name::from_string("Prod.fst"), plv.clone());
        let prodp_snd = Expr::const_(Name::from_string("Prod.snd"), plv);
        let eq_u = Expr::const_(Name::from_string("Eq"), vec![Level::succ(up_lvl.clone())]);
        let eq_refl_u = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(up_lvl.clone())],
        );
        let pab = |a: &Expr, bb: &Expr| Expr::apps(prodp.clone(), [a.clone(), bb.clone()]);
        let mkp = |a: &Expr, bb: &Expr, x: &Expr, y: &Expr| {
            Expr::apps(
                prodp_mk.clone(),
                [a.clone(), bb.clone(), x.clone(), y.clone()],
            )
        };
        let fstp = |a: &Expr, bb: &Expr, p: &Expr| {
            Expr::apps(prodp_fst.clone(), [a.clone(), bb.clone(), p.clone()])
        };
        let sndp = |a: &Expr, bb: &Expr, p: &Expr| {
            Expr::apps(prodp_snd.clone(), [a.clone(), bb.clone(), p.clone()])
        };
        let lensp_app = |a: &Expr, bb: &Expr, p: &Expr, x: &Expr| {
            Expr::apps(
                Expr::const_(
                    Name::from_string(GIVEBACK_AGG_FST_LENS_P),
                    vec![up_lvl.clone()],
                ),
                [a.clone(), bb.clone(), p.clone(), x.clone()],
            )
        };

        // fstLensP : {A B : Type u} → Prod A B → A → Prod A B := λ {A B} p a => Prod.mk a p.snd
        let lens_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let t = Expr::arrow(pab(&a, &bb), Expr::arrow(a.clone(), pab(&a, &bb)));
            let t = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), t);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), t))
        };
        let lens_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (x_id, x) = b.fresh_local(a.clone());
            let body = mkp(&a, &bb, &x, &sndp(&a, &bb, &p));
            let e = b.mk_lam(x_id, BinderInfo::Default, a.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_AGG_FST_LENS_P),
            level_params: vec![up.clone()],
            type_: lens_type,
            value: lens_val,
            is_reducible: true,
        })?;

        // putGet : {A B} → ∀ p a, (fstLensP p a).fst = a   (proj-ι)
        let pg_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (x_id, x) = b.fresh_local(a.clone());
            let lhs = fstp(&a, &bb, &lensp_app(&a, &bb, &p, &x));
            let concl = Expr::apps(eq_u.clone(), [a.clone(), lhs, x.clone()]);
            let e = b.mk_pi(x_id, BinderInfo::Default, a.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let pg_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, _p) = b.fresh_local(pab(&a, &bb));
            let (x_id, x) = b.fresh_local(a.clone());
            let refl = Expr::apps(eq_refl_u.clone(), [a.clone(), x.clone()]);
            let e = b.mk_lam(x_id, BinderInfo::Default, a.clone(), refl);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_FST_LENS_P_PUTGET),
            level_params: vec![up.clone()],
            type_: pg_type,
            value: pg_val,
        })?;

        // getPut : {A B} → ∀ p, fstLensP p p.fst = p   (structure-eta on Prod)
        let gp_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let lhs = lensp_app(&a, &bb, &p, &fstp(&a, &bb, &p));
            let concl = Expr::apps(eq_u.clone(), [pab(&a, &bb), lhs, p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, pab(&a, &bb), concl);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let gp_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let refl = Expr::apps(eq_refl_u.clone(), [pab(&a, &bb), p.clone()]);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), refl);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_FST_LENS_P_GETPUT),
            level_params: vec![up.clone()],
            type_: gp_type,
            value: gp_val,
        })?;

        // frame : {A B} → ∀ p a, (fstLensP p a).snd = p.snd   (proj-ι, sibling untouched)
        let fr_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (x_id, x) = b.fresh_local(a.clone());
            let lhs = sndp(&a, &bb, &lensp_app(&a, &bb, &p, &x));
            let concl = Expr::apps(eq_u.clone(), [bb.clone(), lhs, sndp(&a, &bb, &p)]);
            let e = b.mk_pi(x_id, BinderInfo::Default, a.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let fr_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (x_id, _x) = b.fresh_local(a.clone());
            let refl = Expr::apps(eq_refl_u.clone(), [bb.clone(), sndp(&a, &bb, &p)]);
            let e = b.mk_lam(x_id, BinderInfo::Default, a.clone(), refl);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_FST_LENS_P_FRAME),
            level_params: vec![up],
            type_: fr_type,
            value: fr_val,
        })?;

        // ── The SIBLING projection: sndLensP.{u} {A B : Type u} p b = Prod.mk p.fst b.
        //    Together with fstLensP this is the complete pair lens, generically. Same
        //    universe machinery (up_lvl, type_u, eq_u, pab/mkp/fstp/sndp all reused).
        let up2 = Name::from_string("u");
        let snd_lensp_app = |a: &Expr, bb: &Expr, p: &Expr, y: &Expr| {
            Expr::apps(
                Expr::const_(
                    Name::from_string(GIVEBACK_AGG_SND_LENS_P),
                    vec![up_lvl.clone()],
                ),
                [a.clone(), bb.clone(), p.clone(), y.clone()],
            )
        };
        // sndLensP : {A B : Type u} → Prod A B → B → Prod A B := λ {A B} p b => Prod.mk p.fst b
        let s_lens_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let t = Expr::arrow(pab(&a, &bb), Expr::arrow(bb.clone(), pab(&a, &bb)));
            let t = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), t);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), t))
        };
        let s_lens_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (y_id, y) = b.fresh_local(bb.clone());
            let body = mkp(&a, &bb, &fstp(&a, &bb, &p), &y);
            let e = b.mk_lam(y_id, BinderInfo::Default, bb.clone(), body);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_AGG_SND_LENS_P),
            level_params: vec![up2.clone()],
            type_: s_lens_type,
            value: s_lens_val,
            is_reducible: true,
        })?;

        // putGet : {A B} → ∀ p b, (sndLensP p b).snd = b   (proj-ι)
        let spg_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (y_id, y) = b.fresh_local(bb.clone());
            let lhs = sndp(&a, &bb, &snd_lensp_app(&a, &bb, &p, &y));
            let concl = Expr::apps(eq_u.clone(), [bb.clone(), lhs, y.clone()]);
            let e = b.mk_pi(y_id, BinderInfo::Default, bb.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let spg_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, _p) = b.fresh_local(pab(&a, &bb));
            let (y_id, y) = b.fresh_local(bb.clone());
            let refl = Expr::apps(eq_refl_u.clone(), [bb.clone(), y.clone()]);
            let e = b.mk_lam(y_id, BinderInfo::Default, bb.clone(), refl);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_SND_LENS_P_PUTGET),
            level_params: vec![up2.clone()],
            type_: spg_type,
            value: spg_val,
        })?;

        // getPut : {A B} → ∀ p, sndLensP p p.snd = p   (structure-eta)
        let sgp_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let lhs = snd_lensp_app(&a, &bb, &p, &sndp(&a, &bb, &p));
            let concl = Expr::apps(eq_u.clone(), [pab(&a, &bb), lhs, p.clone()]);
            let e = b.mk_pi(p_id, BinderInfo::Default, pab(&a, &bb), concl);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let sgp_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let refl = Expr::apps(eq_refl_u.clone(), [pab(&a, &bb), p.clone()]);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), refl);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_SND_LENS_P_GETPUT),
            level_params: vec![up2.clone()],
            type_: sgp_type,
            value: sgp_val,
        })?;

        // frame : {A B} → ∀ p b, (sndLensP p b).fst = p.fst   (proj-ι, sibling untouched)
        let sfr_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (y_id, y) = b.fresh_local(bb.clone());
            let lhs = fstp(&a, &bb, &snd_lensp_app(&a, &bb, &p, &y));
            let concl = Expr::apps(eq_u.clone(), [a.clone(), lhs, fstp(&a, &bb, &p)]);
            let e = b.mk_pi(y_id, BinderInfo::Default, bb.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let sfr_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (b_id, bb) = b.fresh_local(type_u.clone());
            let (p_id, p) = b.fresh_local(pab(&a, &bb));
            let (y_id, _y) = b.fresh_local(bb.clone());
            let refl = Expr::apps(eq_refl_u.clone(), [a.clone(), fstp(&a, &bb, &p)]);
            let e = b.mk_lam(y_id, BinderInfo::Default, bb.clone(), refl);
            let e = b.mk_lam(p_id, BinderInfo::Default, pab(&a, &bb), e);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_SND_LENS_P_FRAME),
            level_params: vec![up2],
            type_: sfr_type,
            value: sfr_val,
        })?;

        // ── THE GENERAL n-ary lens: lens COMPOSITION preserves the lens laws. Field-k of
        //    an n-ary struct is a composition of fst/snd lenses down the nested-product
        //    spine, so these two theorems certify EVERY field of EVERY arity — one proof,
        //    not a per-arity family. Abstract lenses over S↔M↔A (all Type u).
        let uc = Name::from_string("u");
        let uc_lvl = Level::param(uc.clone());
        let ucs = Level::succ(uc_lvl.clone());
        let sortu = Expr::sort(ucs.clone());
        let eqc_u = Expr::const_(Name::from_string("Eq"), vec![ucs.clone()]);
        let eq_at = |t: &Expr, a: Expr, b: Expr| Expr::apps(eqc_u.clone(), [t.clone(), a, b]);
        let congr_u = Expr::const_(
            Name::from_string("congrArg"),
            vec![ucs.clone(), ucs.clone()],
        );
        let trans_u = Expr::const_(Name::from_string("Eq.trans"), vec![ucs.clone()]);

        // putGet-composition:
        //   ∀ {S M A}(go:S→M)(po:S→M→S)(gi:M→A)(pi:M→A→M)
        //     (pgo:∀ s m, go(po s m)=m)(pgi:∀ m a, gi(pi m a)=a)(s a),
        //     gi (go (po s (pi (go s) a))) = a
        //   := Eq.trans (congrArg gi (pgo s (pi (go s) a))) (pgi (go s) a)
        let lcp_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s_ty) = b.fresh_local(sortu.clone());
            let (m_id, m_ty) = b.fresh_local(sortu.clone());
            let (a_id, a_ty) = b.fresh_local(sortu.clone());
            let (go_id, go) = b.fresh_local(Expr::arrow(s_ty.clone(), m_ty.clone()));
            let (po_id, po) = b.fresh_local(Expr::arrow(
                s_ty.clone(),
                Expr::arrow(m_ty.clone(), s_ty.clone()),
            ));
            let (gi_id, gi) = b.fresh_local(Expr::arrow(m_ty.clone(), a_ty.clone()));
            let (pi_id, pi) = b.fresh_local(Expr::arrow(
                m_ty.clone(),
                Expr::arrow(a_ty.clone(), m_ty.clone()),
            ));
            let go_a = |x: &Expr| Expr::app(go.clone(), x.clone());
            let po_a = |x: &Expr, y: &Expr| Expr::apps(po.clone(), [x.clone(), y.clone()]);
            let gi_a = |x: &Expr| Expr::app(gi.clone(), x.clone());
            let pi_a = |x: &Expr, y: &Expr| Expr::apps(pi.clone(), [x.clone(), y.clone()]);
            let pgo_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ss_id, ss) = c.fresh_local(s_ty.clone());
                let (mm_id, mm) = c.fresh_local(m_ty.clone());
                let concl = eq_at(&m_ty, go_a(&po_a(&ss, &mm)), mm.clone());
                let e = c.mk_pi(mm_id, BinderInfo::Default, m_ty.clone(), concl);
                c.finish_child(c.mk_pi(ss_id, BinderInfo::Default, s_ty.clone(), e))
            };
            let (pgo_id, _pgo) = b.fresh_local(pgo_ty.clone());
            let pgi_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = c.fresh_local(m_ty.clone());
                let (aa_id, aa) = c.fresh_local(a_ty.clone());
                let concl = eq_at(&a_ty, gi_a(&pi_a(&mm, &aa)), aa.clone());
                let e = c.mk_pi(aa_id, BinderInfo::Default, a_ty.clone(), concl);
                c.finish_child(c.mk_pi(mm_id, BinderInfo::Default, m_ty.clone(), e))
            };
            let (pgi_id, _pgi) = b.fresh_local(pgi_ty.clone());
            let (ss_id, ss) = b.fresh_local(s_ty.clone());
            let (aa_id, aa) = b.fresh_local(a_ty.clone());
            let concl = eq_at(
                &a_ty,
                gi_a(&go_a(&po_a(&ss, &pi_a(&go_a(&ss), &aa)))),
                aa.clone(),
            );
            let e = b.mk_pi(aa_id, BinderInfo::Default, a_ty.clone(), concl);
            let e = b.mk_pi(ss_id, BinderInfo::Default, s_ty.clone(), e);
            let e = b.mk_pi(pgi_id, BinderInfo::Default, pgi_ty, e);
            let e = b.mk_pi(pgo_id, BinderInfo::Default, pgo_ty, e);
            let e = b.mk_pi(
                pi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), Expr::arrow(a_ty.clone(), m_ty.clone())),
                e,
            );
            let e = b.mk_pi(
                gi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), a_ty.clone()),
                e,
            );
            let e = b.mk_pi(
                po_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), Expr::arrow(m_ty.clone(), s_ty.clone())),
                e,
            );
            let e = b.mk_pi(
                go_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), m_ty.clone()),
                e,
            );
            let e = b.mk_pi(a_id, BinderInfo::Implicit, sortu.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Implicit, sortu.clone(), e);
            b.finish(b.mk_pi(s_id, BinderInfo::Implicit, sortu.clone(), e))
        };
        let lcp_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s_ty) = b.fresh_local(sortu.clone());
            let (m_id, m_ty) = b.fresh_local(sortu.clone());
            let (a_id, a_ty) = b.fresh_local(sortu.clone());
            let (go_id, go) = b.fresh_local(Expr::arrow(s_ty.clone(), m_ty.clone()));
            let (po_id, po) = b.fresh_local(Expr::arrow(
                s_ty.clone(),
                Expr::arrow(m_ty.clone(), s_ty.clone()),
            ));
            let (gi_id, gi) = b.fresh_local(Expr::arrow(m_ty.clone(), a_ty.clone()));
            let (pi_id, pi) = b.fresh_local(Expr::arrow(
                m_ty.clone(),
                Expr::arrow(a_ty.clone(), m_ty.clone()),
            ));
            let go_a = |x: &Expr| Expr::app(go.clone(), x.clone());
            let po_a = |x: &Expr, y: &Expr| Expr::apps(po.clone(), [x.clone(), y.clone()]);
            let gi_a = |x: &Expr| Expr::app(gi.clone(), x.clone());
            let pi_a = |x: &Expr, y: &Expr| Expr::apps(pi.clone(), [x.clone(), y.clone()]);
            let pgo_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ss_id, ss) = c.fresh_local(s_ty.clone());
                let (mm_id, mm) = c.fresh_local(m_ty.clone());
                let concl = eq_at(&m_ty, go_a(&po_a(&ss, &mm)), mm.clone());
                let e = c.mk_pi(mm_id, BinderInfo::Default, m_ty.clone(), concl);
                c.finish_child(c.mk_pi(ss_id, BinderInfo::Default, s_ty.clone(), e))
            };
            let (pgo_id, pgo) = b.fresh_local(pgo_ty.clone());
            let pgi_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = c.fresh_local(m_ty.clone());
                let (aa_id, aa) = c.fresh_local(a_ty.clone());
                let concl = eq_at(&a_ty, gi_a(&pi_a(&mm, &aa)), aa.clone());
                let e = c.mk_pi(aa_id, BinderInfo::Default, a_ty.clone(), concl);
                c.finish_child(c.mk_pi(mm_id, BinderInfo::Default, m_ty.clone(), e))
            };
            let (pgi_id, pgi) = b.fresh_local(pgi_ty.clone());
            let (ss_id, ss) = b.fresh_local(s_ty.clone());
            let (aa_id, aa) = b.fresh_local(a_ty.clone());
            // x := pi (go s) a ;  congrArg gi (pgo s x) : gi(go(po s x)) = gi x
            let x = pi_a(&go_a(&ss), &aa);
            let pgo_s_x = Expr::apps(pgo.clone(), [ss.clone(), x.clone()]);
            let congr = Expr::apps(
                congr_u.clone(),
                [
                    m_ty.clone(),
                    a_ty.clone(),
                    go_a(&po_a(&ss, &x)),
                    x.clone(),
                    gi.clone(),
                    pgo_s_x,
                ],
            );
            let pgi_gos_a = Expr::apps(pgi.clone(), [go_a(&ss), aa.clone()]);
            // Eq.trans : gi(go(po s x)) = a
            let body = Expr::apps(
                trans_u.clone(),
                [
                    a_ty.clone(),
                    gi_a(&go_a(&po_a(&ss, &x))),
                    gi_a(&x),
                    aa.clone(),
                    congr,
                    pgi_gos_a,
                ],
            );
            let e = b.mk_lam(aa_id, BinderInfo::Default, a_ty.clone(), body);
            let e = b.mk_lam(ss_id, BinderInfo::Default, s_ty.clone(), e);
            let e = b.mk_lam(pgi_id, BinderInfo::Default, pgi_ty, e);
            let e = b.mk_lam(pgo_id, BinderInfo::Default, pgo_ty, e);
            let e = b.mk_lam(
                pi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), Expr::arrow(a_ty.clone(), m_ty.clone())),
                e,
            );
            let e = b.mk_lam(
                gi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), a_ty.clone()),
                e,
            );
            let e = b.mk_lam(
                po_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), Expr::arrow(m_ty.clone(), s_ty.clone())),
                e,
            );
            let e = b.mk_lam(
                go_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), m_ty.clone()),
                e,
            );
            let e = b.mk_lam(a_id, BinderInfo::Implicit, sortu.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Implicit, sortu.clone(), e);
            b.finish(b.mk_lam(s_id, BinderInfo::Implicit, sortu.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_LENS_COMPOSE_PUTGET),
            level_params: vec![uc.clone()],
            type_: lcp_type,
            value: lcp_val,
        })?;

        // getPut-composition:
        //   ∀ {S M A}(go po gi pi)(gpo:∀ s, po s (go s)=s)(gpi:∀ m, pi m (gi m)=m)(s),
        //     po s (pi (go s) (gi (go s))) = s
        //   := Eq.trans (congrArg (po s) (gpi (go s))) (gpo s)
        let lcg_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s_ty) = b.fresh_local(sortu.clone());
            let (m_id, m_ty) = b.fresh_local(sortu.clone());
            let (a_id, a_ty) = b.fresh_local(sortu.clone());
            let (go_id, go) = b.fresh_local(Expr::arrow(s_ty.clone(), m_ty.clone()));
            let (po_id, po) = b.fresh_local(Expr::arrow(
                s_ty.clone(),
                Expr::arrow(m_ty.clone(), s_ty.clone()),
            ));
            let (gi_id, gi) = b.fresh_local(Expr::arrow(m_ty.clone(), a_ty.clone()));
            let (pi_id, pi) = b.fresh_local(Expr::arrow(
                m_ty.clone(),
                Expr::arrow(a_ty.clone(), m_ty.clone()),
            ));
            let go_a = |x: &Expr| Expr::app(go.clone(), x.clone());
            let po_a = |x: &Expr, y: &Expr| Expr::apps(po.clone(), [x.clone(), y.clone()]);
            let gi_a = |x: &Expr| Expr::app(gi.clone(), x.clone());
            let pi_a = |x: &Expr, y: &Expr| Expr::apps(pi.clone(), [x.clone(), y.clone()]);
            let gpo_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ss_id, ss) = c.fresh_local(s_ty.clone());
                let concl = eq_at(&s_ty, po_a(&ss, &go_a(&ss)), ss.clone());
                c.finish_child(c.mk_pi(ss_id, BinderInfo::Default, s_ty.clone(), concl))
            };
            let (gpo_id, _gpo) = b.fresh_local(gpo_ty.clone());
            let gpi_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = c.fresh_local(m_ty.clone());
                let concl = eq_at(&m_ty, pi_a(&mm, &gi_a(&mm)), mm.clone());
                c.finish_child(c.mk_pi(mm_id, BinderInfo::Default, m_ty.clone(), concl))
            };
            let (gpi_id, _gpi) = b.fresh_local(gpi_ty.clone());
            let (ss_id, ss) = b.fresh_local(s_ty.clone());
            let concl = eq_at(
                &s_ty,
                po_a(&ss, &pi_a(&go_a(&ss), &gi_a(&go_a(&ss)))),
                ss.clone(),
            );
            let e = b.mk_pi(ss_id, BinderInfo::Default, s_ty.clone(), concl);
            let e = b.mk_pi(gpi_id, BinderInfo::Default, gpi_ty, e);
            let e = b.mk_pi(gpo_id, BinderInfo::Default, gpo_ty, e);
            let e = b.mk_pi(
                pi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), Expr::arrow(a_ty.clone(), m_ty.clone())),
                e,
            );
            let e = b.mk_pi(
                gi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), a_ty.clone()),
                e,
            );
            let e = b.mk_pi(
                po_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), Expr::arrow(m_ty.clone(), s_ty.clone())),
                e,
            );
            let e = b.mk_pi(
                go_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), m_ty.clone()),
                e,
            );
            let e = b.mk_pi(a_id, BinderInfo::Implicit, sortu.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Implicit, sortu.clone(), e);
            b.finish(b.mk_pi(s_id, BinderInfo::Implicit, sortu.clone(), e))
        };
        let lcg_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s_ty) = b.fresh_local(sortu.clone());
            let (m_id, m_ty) = b.fresh_local(sortu.clone());
            let (a_id, a_ty) = b.fresh_local(sortu.clone());
            let (go_id, go) = b.fresh_local(Expr::arrow(s_ty.clone(), m_ty.clone()));
            let (po_id, po) = b.fresh_local(Expr::arrow(
                s_ty.clone(),
                Expr::arrow(m_ty.clone(), s_ty.clone()),
            ));
            let (gi_id, gi) = b.fresh_local(Expr::arrow(m_ty.clone(), a_ty.clone()));
            let (pi_id, pi) = b.fresh_local(Expr::arrow(
                m_ty.clone(),
                Expr::arrow(a_ty.clone(), m_ty.clone()),
            ));
            let go_a = |x: &Expr| Expr::app(go.clone(), x.clone());
            let po_a = |x: &Expr, y: &Expr| Expr::apps(po.clone(), [x.clone(), y.clone()]);
            let gi_a = |x: &Expr| Expr::app(gi.clone(), x.clone());
            let pi_a = |x: &Expr, y: &Expr| Expr::apps(pi.clone(), [x.clone(), y.clone()]);
            let gpo_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ss_id, ss) = c.fresh_local(s_ty.clone());
                let concl = eq_at(&s_ty, po_a(&ss, &go_a(&ss)), ss.clone());
                c.finish_child(c.mk_pi(ss_id, BinderInfo::Default, s_ty.clone(), concl))
            };
            let (gpo_id, gpo) = b.fresh_local(gpo_ty.clone());
            let gpi_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mm_id, mm) = c.fresh_local(m_ty.clone());
                let concl = eq_at(&m_ty, pi_a(&mm, &gi_a(&mm)), mm.clone());
                c.finish_child(c.mk_pi(mm_id, BinderInfo::Default, m_ty.clone(), concl))
            };
            let (gpi_id, gpi) = b.fresh_local(gpi_ty.clone());
            let (ss_id, ss) = b.fresh_local(s_ty.clone());
            // po s : M → S ;  congrArg (po s) (gpi (go s)) : po s (pi (go s)(gi(go s))) = po s (go s)
            let po_s = Expr::app(po.clone(), ss.clone());
            let gpi_gos = Expr::app(gpi.clone(), go_a(&ss));
            let inner = pi_a(&go_a(&ss), &gi_a(&go_a(&ss)));
            let congr = Expr::apps(
                congr_u.clone(),
                [
                    m_ty.clone(),
                    s_ty.clone(),
                    inner.clone(),
                    go_a(&ss),
                    po_s,
                    gpi_gos,
                ],
            );
            let gpo_s = Expr::app(gpo.clone(), ss.clone());
            let body = Expr::apps(
                trans_u.clone(),
                [
                    s_ty.clone(),
                    po_a(&ss, &inner),
                    po_a(&ss, &go_a(&ss)),
                    ss.clone(),
                    congr,
                    gpo_s,
                ],
            );
            let e = b.mk_lam(ss_id, BinderInfo::Default, s_ty.clone(), body);
            let e = b.mk_lam(gpi_id, BinderInfo::Default, gpi_ty, e);
            let e = b.mk_lam(gpo_id, BinderInfo::Default, gpo_ty, e);
            let e = b.mk_lam(
                pi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), Expr::arrow(a_ty.clone(), m_ty.clone())),
                e,
            );
            let e = b.mk_lam(
                gi_id,
                BinderInfo::Default,
                Expr::arrow(m_ty.clone(), a_ty.clone()),
                e,
            );
            let e = b.mk_lam(
                po_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), Expr::arrow(m_ty.clone(), s_ty.clone())),
                e,
            );
            let e = b.mk_lam(
                go_id,
                BinderInfo::Default,
                Expr::arrow(s_ty.clone(), m_ty.clone()),
                e,
            );
            let e = b.mk_lam(a_id, BinderInfo::Implicit, sortu.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Implicit, sortu.clone(), e);
            b.finish(b.mk_lam(s_id, BinderInfo::Implicit, sortu.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_LENS_COMPOSE_GETPUT),
            level_params: vec![uc.clone()],
            type_: lcg_type,
            value: lcg_val,
        })?;

        // ── POLYMORPHIC nested (p.0.0) give-back: instantiate lensCompose_getPut at two
        //    fst lenses. Deep-field give-back IS a composed lens — general for any A,B,C.
        let uc2 = uc_lvl.clone();
        let prod2c = Expr::const_(Name::from_string("Prod"), vec![uc2.clone(), uc2.clone()]);
        let prod2 = |a: &Expr, b: &Expr| Expr::apps(prod2c.clone(), [a.clone(), b.clone()]);
        let pfstc = Expr::const_(
            Name::from_string("Prod.fst"),
            vec![uc2.clone(), uc2.clone()],
        );
        let flp = Expr::const_(
            Name::from_string(GIVEBACK_AGG_FST_LENS_P),
            vec![uc2.clone()],
        );
        let flp_gp = Expr::const_(
            Name::from_string(GIVEBACK_AGG_FST_LENS_P_GETPUT),
            vec![uc2.clone()],
        );
        let lcg = Expr::const_(
            Name::from_string(GIVEBACK_AGG_LENS_COMPOSE_GETPUT),
            vec![uc2.clone()],
        );
        let nest_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortu.clone());
            let (bb_id, bb) = b.fresh_local(sortu.clone());
            let (c_id, c) = b.fresh_local(sortu.clone());
            let mm = prod2(&a, &bb); // Prod A B
            let ss = prod2(&mm, &c); // Prod (Prod A B) C
            let (s_id, s) = b.fresh_local(ss.clone());
            let fst_o = |x: &Expr| Expr::apps(pfstc.clone(), [mm.clone(), c.clone(), x.clone()]);
            let fst_i = |x: &Expr| Expr::apps(pfstc.clone(), [a.clone(), bb.clone(), x.clone()]);
            let lens_o = |x: &Expr, y: &Expr| {
                Expr::apps(flp.clone(), [mm.clone(), c.clone(), x.clone(), y.clone()])
            };
            let lens_i = |x: &Expr, y: &Expr| {
                Expr::apps(flp.clone(), [a.clone(), bb.clone(), x.clone(), y.clone()])
            };
            let inner = lens_i(&fst_o(&s), &fst_i(&fst_o(&s)));
            let lhs = lens_o(&s, &inner);
            let concl = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![ucs.clone()]),
                [ss.clone(), lhs, s.clone()],
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, ss.clone(), concl);
            let e = b.mk_pi(c_id, BinderInfo::Implicit, sortu.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Implicit, sortu.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, sortu.clone(), e))
        };
        let nest_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortu.clone());
            let (bb_id, bb) = b.fresh_local(sortu.clone());
            let (c_id, c) = b.fresh_local(sortu.clone());
            let mm = prod2(&a, &bb);
            let ss = prod2(&mm, &c);
            // go=Prod.fst mm c, po=fstLensP mm c, gi=Prod.fst a b, pi=fstLensP a b,
            // gpo=fstLensP_getPut mm c, gpi=fstLensP_getPut a b.
            let go = Expr::apps(pfstc.clone(), [mm.clone(), c.clone()]);
            let po = Expr::apps(flp.clone(), [mm.clone(), c.clone()]);
            let gi = Expr::apps(pfstc.clone(), [a.clone(), bb.clone()]);
            let pi = Expr::apps(flp.clone(), [a.clone(), bb.clone()]);
            let gpo = Expr::apps(flp_gp.clone(), [mm.clone(), c.clone()]);
            let gpi = Expr::apps(flp_gp.clone(), [a.clone(), bb.clone()]);
            let body = Expr::apps(
                lcg.clone(),
                [ss.clone(), mm.clone(), a.clone(), go, po, gi, pi, gpo, gpi],
            );
            let e = b.mk_lam(c_id, BinderInfo::Implicit, sortu.clone(), body);
            let e = b.mk_lam(bb_id, BinderInfo::Implicit, sortu.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, sortu.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_AGG_NEST_LENS_GETPUT),
            level_params: vec![uc.clone()],
            type_: nest_type,
            value: nest_val,
        })?;

        Ok(())
    }

    /// Build the **sum-type (enum) give-back** anchor — the genuine Aeneas
    /// backward function for a `&mut` into a VARIANT PAYLOAD of an enum
    /// (`fn f(o: &mut Option<u32>)` mutating the `Some` payload). The backward
    /// function `optSet o v'` does CASE ANALYSIS (`Option.rec`): rebuild the same
    /// variant with payload `v'` if `Some`, frame the `None` variant. Unlike the
    /// aggregate (product) case — where structure eta made `∀ p` laws hold by
    /// `Eq.refl` — sum types have NO eta, so the `∀ o` laws genuinely require the
    /// recursor to split per variant. Proves (axiom-clean):
    ///
    ///   * frame-none `optSet none v' = none`           (per-variant ι)
    ///   * set-some   `optSet (some x) v' = some v'`     (per-variant ι)
    ///   * put-put    `∀ o, optSet (optSet o v1) v2 = optSet o v2`   (Option.rec)
    ///   * round-trip `∀ o, optSelf o = o`              (Option.rec; sum "eta")
    ///   * incr-some  `optIncr (some a) = some (a+1)`    (the `*x += 1` map)
    ///
    /// put-put and round-trip are proved by `Option.rec` over the OPAQUE `o`
    /// (β + ι per constructor), the case-analysis tier a skeptic checks for enums.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Option`) or a
    /// give-back declaration fails to admit / type-check.
    pub fn init_giveback_enum_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_option()?; // Option, Option.none, Option.some, Option.rec
        self.init_bool()?; // Bool, Bool.true/false, Bool.rec (for the tagged-struct bridge)
        self.init_prod()?; // Prod (for the tagged struct Prod Bool Nat)
        self.init_sum()?; // Sum, Sum.inl/inr, Sum.rec (for the Result-style two-payload match)

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        // Option : Type u → Type u, and Nat : Type 0, so the type-param level is 0
        // (`Option.{0} Nat`). Its result `Option Nat : Type 0 = Sort 1`, so EQ over
        // Option-Nat values is at Sort level 1.
        let u0 = Level::zero();
        let one = Level::succ(Level::zero());
        let opt_t = Expr::app(
            Expr::const_(Name::from_string("Option"), vec![u0.clone()]),
            nat.clone(),
        );
        let opt_none = Expr::const_(Name::from_string("Option.none"), vec![u0.clone()]);
        let opt_some = Expr::const_(Name::from_string("Option.some"), vec![u0.clone()]);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

        let none_e = Expr::app(opt_none.clone(), nat.clone()); // Option.none Nat
        let some_e = |a: &Expr| Expr::apps(opt_some.clone(), [nat.clone(), a.clone()]); // Option.some Nat a
        let eq_opt = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [opt_t.clone(), l, r]);
        let refl_opt = |x: Expr| Expr::apps(eq_refl.clone(), [opt_t.clone(), x]);
        // Option.rec.{motive_lvl, 0} — args: [α, motive, noneMinor, someMinor, major]
        let option_rec = |motive_lvl: Level| {
            Expr::const_(
                Name::from_string("Option.rec"),
                vec![motive_lvl, u0.clone()],
            )
        };

        // optSet : Option Nat → Nat → Option Nat
        //   := λ o v => Option.rec.{1,1} Nat (λ _ => Option Nat) none (λ _a => some v) o
        let opt_set_val = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(opt_t.clone());
                c.finish_child(c.mk_lam(m_id, BinderInfo::Default, opt_t.clone(), opt_t.clone()))
            };
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, nat.clone(), some_e(&v)))
            };
            let body = Expr::apps(
                option_rec(one.clone()),
                [nat.clone(), motive, none_e.clone(), some_minor, o.clone()],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(o_id, BinderInfo::Default, opt_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_OPT_SET),
            level_params: vec![],
            type_: Expr::arrow(opt_t.clone(), Expr::arrow(nat.clone(), opt_t.clone())),
            value: opt_set_val,
            is_reducible: true,
        })?;
        let opt_set = Expr::const_(Name::from_string(GIVEBACK_OPT_SET), vec![]);
        let optset = |o: &Expr, v: &Expr| Expr::apps(opt_set.clone(), [o.clone(), v.clone()]);

        // optSelf : Option Nat → Option Nat
        //   := λ o => Option.rec.{1,1} Nat (λ _ => Option Nat) none (λ a => some a) o
        let opt_self_val = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(opt_t.clone());
                c.finish_child(c.mk_lam(m_id, BinderInfo::Default, opt_t.clone(), opt_t.clone()))
            };
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, nat.clone(), some_e(&a)))
            };
            let body = Expr::apps(
                option_rec(one.clone()),
                [nat.clone(), motive, none_e.clone(), some_minor, o.clone()],
            );
            b.finish(b.mk_lam(o_id, BinderInfo::Default, opt_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_OPT_SELF),
            level_params: vec![],
            type_: Expr::arrow(opt_t.clone(), opt_t.clone()),
            value: opt_self_val,
            is_reducible: true,
        })?;
        let opt_self = Expr::const_(Name::from_string(GIVEBACK_OPT_SELF), vec![]);

        // optIncr : Option Nat → Option Nat
        //   := λ o => Option.rec.{1,1} Nat (λ _ => Option Nat) none (λ a => some (a+1)) o
        let one_lit = Expr::nat_lit(1);
        let incr_payload =
            |a: &Expr| some_e(&Expr::apps(nat_add.clone(), [a.clone(), one_lit.clone()]));
        let opt_incr_val = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(opt_t.clone());
                c.finish_child(c.mk_lam(m_id, BinderInfo::Default, opt_t.clone(), opt_t.clone()))
            };
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, nat.clone(), incr_payload(&a)))
            };
            let body = Expr::apps(
                option_rec(one.clone()),
                [nat.clone(), motive, none_e.clone(), some_minor, o.clone()],
            );
            b.finish(b.mk_lam(o_id, BinderInfo::Default, opt_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_OPT_INCR),
            level_params: vec![],
            type_: Expr::arrow(opt_t.clone(), opt_t.clone()),
            value: opt_incr_val,
            is_reducible: true,
        })?;
        let opt_incr = Expr::const_(Name::from_string(GIVEBACK_OPT_INCR), vec![]);

        // frame-none : ∀ v, optSet none v = none   (per-variant ι; no case analysis)
        let frame_none_type = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_opt(optset(&none_e, &v), none_e.clone());
            b.finish(b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl))
        };
        let frame_none_val = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, _v) = b.fresh_local(nat.clone());
            b.finish(b.mk_lam(
                v_id,
                BinderInfo::Default,
                nat.clone(),
                refl_opt(none_e.clone()),
            ))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_OPT_FRAME_NONE),
            level_params: vec![],
            type_: frame_none_type,
            value: frame_none_val,
        })?;

        // set-some : ∀ x v, optSet (some x) v = some v   (per-variant ι)
        let set_some_type = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_opt(optset(&some_e(&x), &v), some_e(&v));
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, nat.clone(), e))
        };
        let set_some_val = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), refl_opt(some_e(&v)));
            b.finish(b.mk_lam(x_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_OPT_SET_SOME),
            level_params: vec![],
            type_: set_some_type,
            value: set_some_val,
        })?;

        // put-put : ∀ o v1 v2, optSet (optSet o v1) v2 = optSet o v2
        //   proof := λ o v1 v2 => Option.rec.{0,1} Nat
        //              (λ oo => optSet (optSet oo v1) v2 = optSet oo v2)
        //              (refl none) (λ a => refl (some v2)) o
        let put_put_type = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let (v2_id, v2) = b.fresh_local(nat.clone());
            let concl = eq_opt(optset(&optset(&o, &v1), &v2), optset(&o, &v2));
            let e = b.mk_pi(v2_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(v1_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(o_id, BinderInfo::Default, opt_t.clone(), e))
        };
        let put_put_val = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let (v2_id, v2) = b.fresh_local(nat.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (oo_id, oo) = c.fresh_local(opt_t.clone());
                let body = eq_opt(optset(&optset(&oo, &v1), &v2), optset(&oo, &v2));
                c.finish_child(c.mk_lam(oo_id, BinderInfo::Default, opt_t.clone(), body))
            };
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(
                    a_id,
                    BinderInfo::Default,
                    nat.clone(),
                    refl_opt(some_e(&v2)),
                ))
            };
            let body = Expr::apps(
                option_rec(Level::zero()),
                [
                    nat.clone(),
                    motive,
                    refl_opt(none_e.clone()),
                    some_minor,
                    o.clone(),
                ],
            );
            let e = b.mk_lam(v2_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(v1_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(o_id, BinderInfo::Default, opt_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_OPT_PUT_PUT),
            level_params: vec![],
            type_: put_put_type,
            value: put_put_val,
        })?;

        // round-trip : ∀ o, optSelf o = o
        //   proof := λ o => Option.rec.{0,1} Nat (λ oo => optSelf oo = oo)
        //              (refl none) (λ a => refl (some a)) o
        let roundtrip_type = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let concl = eq_opt(Expr::app(opt_self.clone(), o.clone()), o.clone());
            b.finish(b.mk_pi(o_id, BinderInfo::Default, opt_t.clone(), concl))
        };
        let roundtrip_val = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (oo_id, oo) = c.fresh_local(opt_t.clone());
                let body = eq_opt(Expr::app(opt_self.clone(), oo.clone()), oo.clone());
                c.finish_child(c.mk_lam(oo_id, BinderInfo::Default, opt_t.clone(), body))
            };
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(
                    a_id,
                    BinderInfo::Default,
                    nat.clone(),
                    refl_opt(some_e(&a)),
                ))
            };
            let body = Expr::apps(
                option_rec(Level::zero()),
                [
                    nat.clone(),
                    motive,
                    refl_opt(none_e.clone()),
                    some_minor,
                    o.clone(),
                ],
            );
            b.finish(b.mk_lam(o_id, BinderInfo::Default, opt_t.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_OPT_ROUNDTRIP),
            level_params: vec![],
            type_: roundtrip_type,
            value: roundtrip_val,
        })?;

        // incr-some : ∀ a, optIncr (some a) = some (a + 1)   (per-variant ι)
        let incr_some_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            let concl = eq_opt(Expr::app(opt_incr.clone(), some_e(&a)), incr_payload(&a));
            b.finish(b.mk_pi(a_id, BinderInfo::Default, nat.clone(), concl))
        };
        let incr_some_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nat.clone());
            b.finish(b.mk_lam(
                a_id,
                BinderInfo::Default,
                nat.clone(),
                refl_opt(incr_payload(&a)),
            ))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_OPT_INCR_SOME),
            level_params: vec![],
            type_: incr_some_type,
            value: incr_some_val,
        })?;

        // ── INDUCTIVE BRIDGE: the tagged-struct (Prod Bool Nat = {isSome, payload})
        //    enum give-back CORRESPONDS to the inductive optIncr. Pure math — no
        //    compiler-lowering assumption; proved by Option.rec + Bool.rec ι.
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_rec = |lvl: Level| Expr::const_(Name::from_string("Bool.rec"), vec![lvl]);
        let plv = vec![u0.clone(), u0.clone()];
        let prod = Expr::const_(Name::from_string("Prod"), plv.clone());
        let prod_mk = Expr::const_(Name::from_string("Prod.mk"), plv.clone());
        let prod_fst = Expr::const_(Name::from_string("Prod.fst"), plv.clone());
        let prod_snd = Expr::const_(Name::from_string("Prod.snd"), plv);
        let tagged_t = Expr::apps(prod.clone(), [bool_c.clone(), nat.clone()]);
        let mkt = |t: &Expr, p: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [bool_c.clone(), nat.clone(), t.clone(), p.clone()],
            )
        };
        let fstt =
            |p: &Expr| Expr::apps(prod_fst.clone(), [bool_c.clone(), nat.clone(), p.clone()]);
        let sndt =
            |p: &Expr| Expr::apps(prod_snd.clone(), [bool_c.clone(), nat.clone(), p.clone()]);

        // optToTagged : Option Nat → Prod Bool Nat
        //   := λ o => Option.rec (λ_ => tagged) (mk false 0) (λ a => mk true a) o
        let to_tagged_val = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = d.fresh_local(opt_t.clone());
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, opt_t.clone(), tagged_t.clone()))
            };
            let none_minor = mkt(&bfalse, &Expr::nat_lit(0));
            let some_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = d.fresh_local(nat.clone());
                d.finish_child(d.mk_lam(a_id, BinderInfo::Default, nat.clone(), mkt(&btrue, &a)))
            };
            let body = Expr::apps(
                option_rec(one.clone()),
                [nat.clone(), motive, none_minor, some_minor, o.clone()],
            );
            b.finish(b.mk_lam(o_id, BinderInfo::Default, opt_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_OPT_TO_TAGGED),
            level_params: vec![],
            type_: Expr::arrow(opt_t.clone(), tagged_t.clone()),
            value: to_tagged_val,
            is_reducible: true,
        })?;

        // optFromTagged : Prod Bool Nat → Option Nat
        //   := λ p => Bool.rec (λ_ => Option Nat) none (some p.snd) p.fst
        let from_tagged_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(tagged_t.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = d.fresh_local(bool_c.clone());
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, bool_c.clone(), opt_t.clone()))
            };
            let body = Expr::apps(
                bool_rec(one.clone()),
                [motive, none_e.clone(), some_e(&sndt(&p)), fstt(&p)],
            );
            b.finish(b.mk_lam(p_id, BinderInfo::Default, tagged_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_OPT_FROM_TAGGED),
            level_params: vec![],
            type_: Expr::arrow(tagged_t.clone(), opt_t.clone()),
            value: from_tagged_val,
            is_reducible: true,
        })?;

        // taggedOptIncr : Prod Bool Nat → Prod Bool Nat
        //   := λ p => mk p.fst (Bool.rec (λ_ => Nat) p.snd (p.snd + 1) p.fst)
        let tagged_incr_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(tagged_t.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = d.fresh_local(bool_c.clone());
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, bool_c.clone(), nat.clone()))
            };
            let inc = Expr::apps(nat_add.clone(), [sndt(&p), Expr::nat_lit(1)]);
            let new_payload = Expr::apps(bool_rec(one.clone()), [motive, sndt(&p), inc, fstt(&p)]);
            let body = mkt(&fstt(&p), &new_payload);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, tagged_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_OPT_TAGGED_INCR),
            level_params: vec![],
            type_: Expr::arrow(tagged_t.clone(), tagged_t.clone()),
            value: tagged_incr_val,
            is_reducible: true,
        })?;

        let opt_incr = Expr::const_(Name::from_string(GIVEBACK_OPT_INCR), vec![]);
        let to_tagged = Expr::const_(Name::from_string(GIVEBACK_OPT_TO_TAGGED), vec![]);
        let from_tagged = Expr::const_(Name::from_string(GIVEBACK_OPT_FROM_TAGGED), vec![]);
        let tagged_incr = Expr::const_(Name::from_string(GIVEBACK_OPT_TAGGED_INCR), vec![]);
        let bridge_lhs = |o: &Expr| {
            Expr::app(
                from_tagged.clone(),
                Expr::app(tagged_incr.clone(), Expr::app(to_tagged.clone(), o.clone())),
            )
        };

        // optTaggedBridge : ∀ o, optFromTagged (taggedOptIncr (optToTagged o)) = optIncr o
        let bridge_type = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let concl = eq_opt(bridge_lhs(&o), Expr::app(opt_incr.clone(), o.clone()));
            b.finish(b.mk_pi(o_id, BinderInfo::Default, opt_t.clone(), concl))
        };
        let bridge_val = {
            let mut b = EnvDeclBuilder::new();
            let (o_id, o) = b.fresh_local(opt_t.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = d.fresh_local(opt_t.clone());
                let eq = eq_opt(bridge_lhs(&m), Expr::app(opt_incr.clone(), m.clone()));
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, opt_t.clone(), eq))
            };
            // none case: both sides ι-reduce to none.
            let none_minor = refl_opt(none_e.clone());
            // some a: both sides ι-reduce to some (a+1).
            let some_minor = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = d.fresh_local(nat.clone());
                let val = some_e(&Expr::apps(nat_add.clone(), [a.clone(), Expr::nat_lit(1)]));
                d.finish_child(d.mk_lam(a_id, BinderInfo::Default, nat.clone(), refl_opt(val)))
            };
            // Prop motive ⇒ Option.rec.{0, 0}.
            let body = Expr::apps(
                option_rec(Level::zero()),
                [nat.clone(), motive, none_minor, some_minor, o.clone()],
            );
            b.finish(b.mk_lam(o_id, BinderInfo::Default, opt_t.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_OPT_TAGGED_BRIDGE),
            level_params: vec![],
            type_: bridge_type,
            value: bridge_val,
        })?;

        // ── RESULT-STYLE two-payload pattern match: `&mut Sum Nat Nat` (Rust
        //    `&mut Result<T,E>`) incrementing the payload in BOTH arms. Generalizes the
        //    Option give-back (payload-free `None` arm) to a sum with two distinct payloads;
        //    proved by Sum.rec case analysis (per-arm Eq.refl via Nat.sub ι).
        let sum_lv = vec![u0.clone(), u0.clone()];
        let sum_c = Expr::const_(Name::from_string("Sum"), sum_lv.clone());
        let sum_t = Expr::apps(sum_c.clone(), [nat.clone(), nat.clone()]);
        let sum_inl = Expr::const_(Name::from_string("Sum.inl"), sum_lv.clone());
        let sum_inr = Expr::const_(Name::from_string("Sum.inr"), sum_lv.clone());
        let inl = |a: &Expr| Expr::apps(sum_inl.clone(), [nat.clone(), nat.clone(), a.clone()]);
        let inr = |b: &Expr| Expr::apps(sum_inr.clone(), [nat.clone(), nat.clone(), b.clone()]);
        let sum_rec = |w: Level| {
            Expr::const_(
                Name::from_string("Sum.rec"),
                vec![w, u0.clone(), u0.clone()],
            )
        };
        let eq_sum = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [sum_t.clone(), l, r]);
        let refl_sum = |x: Expr| Expr::apps(eq_refl.clone(), [sum_t.clone(), x]);
        let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let one_lit2 = Expr::nat_lit(1);
        // Build λ s => Sum.rec.{1,0,0} Nat Nat (λ_=>Sum) (λ a => inl (op a)) (λ b => inr (op b)) s
        let build_map = |op: &dyn Fn(&Expr) -> Expr| {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(sum_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(sum_t.clone());
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, sum_t.clone(), sum_t.clone()))
            };
            let inl_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, nat.clone(), inl(&op(&a))))
            };
            let inr_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(bb_id, BinderInfo::Default, nat.clone(), inr(&op(&bb))))
            };
            let body = Expr::apps(
                sum_rec(one.clone()),
                [
                    nat.clone(),
                    nat.clone(),
                    motive,
                    inl_minor,
                    inr_minor,
                    s.clone(),
                ],
            );
            b.finish(b.mk_lam(s_id, BinderInfo::Default, sum_t.clone(), body))
        };
        let incr_op = |x: &Expr| Expr::apps(nat_add.clone(), [x.clone(), one_lit2.clone()]);
        let decr_op = |x: &Expr| Expr::apps(nat_sub.clone(), [x.clone(), one_lit2.clone()]);
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_SUM_INCR),
            level_params: vec![],
            type_: Expr::arrow(sum_t.clone(), sum_t.clone()),
            value: build_map(&incr_op),
            is_reducible: true,
        })?;
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_SUM_INCR_BACK),
            level_params: vec![],
            type_: Expr::arrow(sum_t.clone(), sum_t.clone()),
            value: build_map(&decr_op),
            is_reducible: true,
        })?;
        let sum_incr = Expr::const_(Name::from_string(GIVEBACK_SUM_INCR), vec![]);
        let sum_incr_back = Expr::const_(Name::from_string(GIVEBACK_SUM_INCR_BACK), vec![]);
        let round = |s: &Expr| {
            Expr::app(
                sum_incr_back.clone(),
                Expr::app(sum_incr.clone(), s.clone()),
            )
        };
        // sumIncr_roundTrip : ∀ s, sumIncrBack (sumIncr s) = s   (Sum.rec, per-arm refl)
        let srt_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(sum_t.clone());
            let concl = eq_sum(round(&s), s.clone());
            b.finish(b.mk_pi(s_id, BinderInfo::Default, sum_t.clone(), concl))
        };
        let srt_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(sum_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(sum_t.clone());
                let body = eq_sum(round(&x), x.clone());
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, sum_t.clone(), body))
            };
            let inl_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(a_id, BinderInfo::Default, nat.clone(), refl_sum(inl(&a))))
            };
            let inr_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(
                    bb_id,
                    BinderInfo::Default,
                    nat.clone(),
                    refl_sum(inr(&bb)),
                ))
            };
            let body = Expr::apps(
                sum_rec(Level::zero()),
                [
                    nat.clone(),
                    nat.clone(),
                    motive,
                    inl_minor,
                    inr_minor,
                    s.clone(),
                ],
            );
            b.finish(b.mk_lam(s_id, BinderInfo::Default, sum_t.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_SUM_ROUNDTRIP),
            level_params: vec![],
            type_: srt_type,
            value: srt_val,
        })?;

        // ── POLYMORPHIC two-payload match: `Sum A B` over ANY payload types A,B (Type w)
        //    and ANY per-arm reversible ops fa,fb. Anti-catalog generalization of the Nat
        //    Sum give-back. Proof: Sum.rec; each arm rewrites via congrArg on inl/inr.
        let wname = Name::from_string("w");
        let wl = Level::param(wname.clone());
        let wls = Level::succ(wl.clone());
        let sortw = Expr::sort(wls.clone());
        let sum_lw = vec![wl.clone(), wl.clone()];
        let sumw = |a: &Expr, b: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Sum"), sum_lw.clone()),
                [a.clone(), b.clone()],
            )
        };
        let inl_w = |a: &Expr, b: &Expr, x: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Sum.inl"), sum_lw.clone()),
                [a.clone(), b.clone(), x.clone()],
            )
        };
        let inr_w = |a: &Expr, b: &Expr, x: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Sum.inr"), sum_lw.clone()),
                [a.clone(), b.clone(), x.clone()],
            )
        };
        let inl_fn = |a: &Expr, b: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Sum.inl"), sum_lw.clone()),
                [a.clone(), b.clone()],
            )
        };
        let inr_fn = |a: &Expr, b: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Sum.inr"), sum_lw.clone()),
                [a.clone(), b.clone()],
            )
        };
        let sumrec_w = |mlvl: Level| {
            Expr::const_(
                Name::from_string("Sum.rec"),
                vec![mlvl, wl.clone(), wl.clone()],
            )
        };
        let eqc_w = Expr::const_(Name::from_string("Eq"), vec![wls.clone()]);
        let congr_w = Expr::const_(
            Name::from_string("congrArg"),
            vec![wls.clone(), wls.clone()],
        );
        let ata = |a: &Expr| Expr::arrow(a.clone(), a.clone());

        // sumMap : {A B : Type w} → (A→A) → (B→B) → Sum A B → Sum A B
        let smap_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortw.clone());
            let (bb_id, bb) = b.fresh_local(sortw.clone());
            let t = Expr::arrow(
                ata(&a),
                Expr::arrow(ata(&bb), Expr::arrow(sumw(&a, &bb), sumw(&a, &bb))),
            );
            let t = b.mk_pi(bb_id, BinderInfo::Implicit, sortw.clone(), t);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, sortw.clone(), t))
        };
        let smap_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortw.clone());
            let (bb_id, bb) = b.fresh_local(sortw.clone());
            let (fa_id, fa) = b.fresh_local(ata(&a));
            let (fb_id, fb) = b.fresh_local(ata(&bb));
            let (s_id, s) = b.fresh_local(sumw(&a, &bb));
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(sumw(&a, &bb));
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, sumw(&a, &bb), sumw(&a, &bb)))
            };
            let inl_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(a.clone());
                c.finish_child(c.mk_lam(
                    x_id,
                    BinderInfo::Default,
                    a.clone(),
                    inl_w(&a, &bb, &Expr::app(fa.clone(), x.clone())),
                ))
            };
            let inr_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(bb.clone());
                c.finish_child(c.mk_lam(
                    x_id,
                    BinderInfo::Default,
                    bb.clone(),
                    inr_w(&a, &bb, &Expr::app(fb.clone(), x.clone())),
                ))
            };
            let rec = Expr::apps(
                sumrec_w(wls.clone()),
                [
                    a.clone(),
                    bb.clone(),
                    motive,
                    inl_minor,
                    inr_minor,
                    s.clone(),
                ],
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, sumw(&a, &bb), rec);
            let e = b.mk_lam(fb_id, BinderInfo::Default, ata(&bb), e);
            let e = b.mk_lam(fa_id, BinderInfo::Default, ata(&a), e);
            let e = b.mk_lam(bb_id, BinderInfo::Implicit, sortw.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, sortw.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_SUM_MAP),
            level_params: vec![wname.clone()],
            type_: smap_type,
            value: smap_val,
            is_reducible: true,
        })?;
        let smap = |a: &Expr, bb: &Expr, fa: &Expr, fb: &Expr, s: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string(GIVEBACK_SUM_MAP), vec![wl.clone()]),
                [a.clone(), bb.clone(), fa.clone(), fb.clone(), s.clone()],
            )
        };
        let eq_sw =
            |a: &Expr, bb: &Expr, l: Expr, r: Expr| Expr::apps(eqc_w.clone(), [sumw(a, bb), l, r]);

        // sumMap_roundTrip : {A B}(fa fia fb fib)(ha:∀a,fia(fa a)=a)(hb:∀b,fib(fb b)=b) →
        //                      ∀ s, sumMap fia fib (sumMap fa fb s) = s
        let eq_a = |a: &Expr, l: Expr, r: Expr| Expr::apps(eqc_w.clone(), [a.clone(), l, r]);
        let hyp_ty = |ty: &Expr, f: &Expr, fi: &Expr, b: &EnvDeclBuilder| {
            let mut c = EnvDeclBuilder::child_of(b);
            let (x_id, x) = c.fresh_local(ty.clone());
            let concl = eq_a(
                ty,
                Expr::app(fi.clone(), Expr::app(f.clone(), x.clone())),
                x.clone(),
            );
            c.finish_child(c.mk_pi(x_id, BinderInfo::Default, ty.clone(), concl))
        };
        let smrt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortw.clone());
            let (bb_id, bb) = b.fresh_local(sortw.clone());
            let (fa_id, fa) = b.fresh_local(ata(&a));
            let (fia_id, fia) = b.fresh_local(ata(&a));
            let (fb_id, fb) = b.fresh_local(ata(&bb));
            let (fib_id, fib) = b.fresh_local(ata(&bb));
            let ha_ty = hyp_ty(&a, &fa, &fia, &b);
            let (ha_id, _ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = hyp_ty(&bb, &fb, &fib, &b);
            let (hb_id, _hb) = b.fresh_local(hb_ty.clone());
            let (s_id, s) = b.fresh_local(sumw(&a, &bb));
            let concl = eq_sw(
                &a,
                &bb,
                smap(&a, &bb, &fia, &fib, &smap(&a, &bb, &fa, &fb, &s)),
                s.clone(),
            );
            let e = b.mk_pi(s_id, BinderInfo::Default, sumw(&a, &bb), concl);
            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(fib_id, BinderInfo::Default, ata(&bb), e);
            let e = b.mk_pi(fb_id, BinderInfo::Default, ata(&bb), e);
            let e = b.mk_pi(fia_id, BinderInfo::Default, ata(&a), e);
            let e = b.mk_pi(fa_id, BinderInfo::Default, ata(&a), e);
            let e = b.mk_pi(bb_id, BinderInfo::Implicit, sortw.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, sortw.clone(), e))
        };
        let smrt_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortw.clone());
            let (bb_id, bb) = b.fresh_local(sortw.clone());
            let (fa_id, fa) = b.fresh_local(ata(&a));
            let (fia_id, fia) = b.fresh_local(ata(&a));
            let (fb_id, fb) = b.fresh_local(ata(&bb));
            let (fib_id, fib) = b.fresh_local(ata(&bb));
            let ha_ty = hyp_ty(&a, &fa, &fia, &b);
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = hyp_ty(&bb, &fb, &fib, &b);
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let (s_id, s) = b.fresh_local(sumw(&a, &bb));
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ss_id, ss) = c.fresh_local(sumw(&a, &bb));
                let body = eq_sw(
                    &a,
                    &bb,
                    smap(&a, &bb, &fia, &fib, &smap(&a, &bb, &fa, &fb, &ss)),
                    ss.clone(),
                );
                c.finish_child(c.mk_lam(ss_id, BinderInfo::Default, sumw(&a, &bb), body))
            };
            // inl arm: congrArg inl (ha x) : inl (fia (fa x)) = inl x
            let inl_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(a.clone());
                let body = Expr::apps(
                    congr_w.clone(),
                    [
                        a.clone(),
                        sumw(&a, &bb),
                        Expr::app(fia.clone(), Expr::app(fa.clone(), x.clone())),
                        x.clone(),
                        inl_fn(&a, &bb),
                        Expr::app(ha.clone(), x.clone()),
                    ],
                );
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, a.clone(), body))
            };
            let inr_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(bb.clone());
                let body = Expr::apps(
                    congr_w.clone(),
                    [
                        bb.clone(),
                        sumw(&a, &bb),
                        Expr::app(fib.clone(), Expr::app(fb.clone(), x.clone())),
                        x.clone(),
                        inr_fn(&a, &bb),
                        Expr::app(hb.clone(), x.clone()),
                    ],
                );
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bb.clone(), body))
            };
            let rec = Expr::apps(
                sumrec_w(Level::zero()),
                [
                    a.clone(),
                    bb.clone(),
                    motive,
                    inl_minor,
                    inr_minor,
                    s.clone(),
                ],
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, sumw(&a, &bb), rec);
            let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_lam(fib_id, BinderInfo::Default, ata(&bb), e);
            let e = b.mk_lam(fb_id, BinderInfo::Default, ata(&bb), e);
            let e = b.mk_lam(fia_id, BinderInfo::Default, ata(&a), e);
            let e = b.mk_lam(fa_id, BinderInfo::Default, ata(&a), e);
            let e = b.mk_lam(bb_id, BinderInfo::Implicit, sortw.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, sortw.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_SUM_MAP_ROUNDTRIP),
            level_params: vec![wname.clone()],
            type_: smrt_type,
            value: smrt_val,
        })?;

        // ── POLYMORPHIC Option match: `Option A` over ANY payload type A (Type v) and ANY
        //    reversible op f. Completes pattern-match generality alongside sumMap.
        let vname = Name::from_string("v");
        let vl = Level::param(vname.clone());
        let vs = Level::succ(vl.clone());
        let sortv = Expr::sort(vs.clone());
        let opt_v = |a: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Option"), vec![vl.clone()]),
                a.clone(),
            )
        };
        let some_v = |a: &Expr, x: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Option.some"), vec![vl.clone()]),
                [a.clone(), x.clone()],
            )
        };
        let none_v = |a: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Option.none"), vec![vl.clone()]),
                a.clone(),
            )
        };
        let some_fn_v = |a: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Option.some"), vec![vl.clone()]),
                a.clone(),
            )
        };
        let optrec_v =
            |mlvl: Level| Expr::const_(Name::from_string("Option.rec"), vec![mlvl, vl.clone()]);
        let eqc_v = Expr::const_(Name::from_string("Eq"), vec![vs.clone()]);
        let congr_v = Expr::const_(Name::from_string("congrArg"), vec![vs.clone(), vs.clone()]);
        let atav = |a: &Expr| Expr::arrow(a.clone(), a.clone());

        // optMap : {A : Type v} → (A→A) → Option A → Option A
        let omap_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortv.clone());
            let t = Expr::arrow(atav(&a), Expr::arrow(opt_v(&a), opt_v(&a)));
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, sortv.clone(), t))
        };
        let omap_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortv.clone());
            let (f_id, f) = b.fresh_local(atav(&a));
            let (o_id, o) = b.fresh_local(opt_v(&a));
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(opt_v(&a));
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, opt_v(&a), opt_v(&a)))
            };
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(a.clone());
                c.finish_child(c.mk_lam(
                    x_id,
                    BinderInfo::Default,
                    a.clone(),
                    some_v(&a, &Expr::app(f.clone(), x.clone())),
                ))
            };
            let rec = Expr::apps(
                optrec_v(vs.clone()),
                [a.clone(), motive, none_v(&a), some_minor, o.clone()],
            );
            let e = b.mk_lam(o_id, BinderInfo::Default, opt_v(&a), rec);
            let e = b.mk_lam(f_id, BinderInfo::Default, atav(&a), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, sortv.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_OPT_MAP),
            level_params: vec![vname.clone()],
            type_: omap_type,
            value: omap_val,
            is_reducible: true,
        })?;
        let omap = |a: &Expr, f: &Expr, o: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string(GIVEBACK_OPT_MAP), vec![vl.clone()]),
                [a.clone(), f.clone(), o.clone()],
            )
        };
        let eq_ov = |a: &Expr, l: Expr, r: Expr| Expr::apps(eqc_v.clone(), [opt_v(a), l, r]);
        let eq_av = |a: &Expr, l: Expr, r: Expr| Expr::apps(eqc_v.clone(), [a.clone(), l, r]);
        let refl_ov = |a: &Expr, x: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![vs.clone()]),
                [opt_v(a), x],
            )
        };

        // optMap_roundTrip : {A}(f finv)(hinv:∀a,finv(f a)=a) → ∀ o, optMap finv (optMap f o) = o
        let ohyp = |a: &Expr, f: &Expr, fi: &Expr, b: &EnvDeclBuilder| {
            let mut c = EnvDeclBuilder::child_of(b);
            let (x_id, x) = c.fresh_local(a.clone());
            let concl = eq_av(
                a,
                Expr::app(fi.clone(), Expr::app(f.clone(), x.clone())),
                x.clone(),
            );
            c.finish_child(c.mk_pi(x_id, BinderInfo::Default, a.clone(), concl))
        };
        let ort_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortv.clone());
            let (f_id, f) = b.fresh_local(atav(&a));
            let (fi_id, fi) = b.fresh_local(atav(&a));
            let h_ty = ohyp(&a, &f, &fi, &b);
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let (o_id, o) = b.fresh_local(opt_v(&a));
            let concl = eq_ov(&a, omap(&a, &fi, &omap(&a, &f, &o)), o.clone());
            let e = b.mk_pi(o_id, BinderInfo::Default, opt_v(&a), concl);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
            let e = b.mk_pi(fi_id, BinderInfo::Default, atav(&a), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, atav(&a), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, sortv.clone(), e))
        };
        let ort_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(sortv.clone());
            let (f_id, f) = b.fresh_local(atav(&a));
            let (fi_id, fi) = b.fresh_local(atav(&a));
            let h_ty = ohyp(&a, &f, &fi, &b);
            let (h_id, h) = b.fresh_local(h_ty.clone());
            let (o_id, o) = b.fresh_local(opt_v(&a));
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (oo_id, oo) = c.fresh_local(opt_v(&a));
                let body = eq_ov(&a, omap(&a, &fi, &omap(&a, &f, &oo)), oo.clone());
                c.finish_child(c.mk_lam(oo_id, BinderInfo::Default, opt_v(&a), body))
            };
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(a.clone());
                let body = Expr::apps(
                    congr_v.clone(),
                    [
                        a.clone(),
                        opt_v(&a),
                        Expr::app(fi.clone(), Expr::app(f.clone(), x.clone())),
                        x.clone(),
                        some_fn_v(&a),
                        Expr::app(h.clone(), x.clone()),
                    ],
                );
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, a.clone(), body))
            };
            let rec = Expr::apps(
                optrec_v(Level::zero()),
                [
                    a.clone(),
                    motive,
                    refl_ov(&a, none_v(&a)),
                    some_minor,
                    o.clone(),
                ],
            );
            let e = b.mk_lam(o_id, BinderInfo::Default, opt_v(&a), rec);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, e);
            let e = b.mk_lam(fi_id, BinderInfo::Default, atav(&a), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, atav(&a), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, sortv.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_OPT_MAP_ROUNDTRIP),
            level_params: vec![vname.clone()],
            type_: ort_type,
            value: ort_val,
        })?;

        Ok(())
    }

    /// Build the **recursive give-back** anchor — the `list_nth_mut` tier: a
    /// `&mut` into a `List<Nat>`. The give-back must reconstruct an
    /// arbitrarily-deep recursive structure, so its round-trip law needs genuine
    /// STRUCTURAL INDUCTION (not the per-variant ι of the enum case, nor the eta
    /// of the product case). Defines `listSelf` (rebuild = `map id`) and `listIncr`
    /// (`map (+1)` — the give-back of `*x += 1` over every element), both by
    /// `List.rec`, and proves (axiom-clean):
    ///
    ///   * listSelf-cons `listSelf (cons h t) = cons h (listSelf t)`   (ι)
    ///   * **round-trip** `∀ l, listSelf l = l`   (`List.rec` INDUCTION; the cons
    ///     minor consumes the recursion hypothesis `ih : listSelf t = t` and lifts
    ///     it through `cons h` via `congrArg`)
    ///   * incr-cons `listIncr (cons h t) = cons (h+1) (listIncr t)`   (ι)
    ///
    /// The round-trip is the load-bearing induction `list_nth_mut`'s give-back
    /// soundness rests on — the recursive-data capability a skeptic demands.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `List`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_list_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?; // also registers congrArg
        self.init_list()?; // List, List.nil, List.cons, List.rec

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        // List : Type u → Type u; Nat : Type 0 ⇒ type param level 0 (`List.{0} Nat`).
        // `List Nat : Type 0 = Sort 1`, so Eq over List-Nat values is `Eq.{1}`.
        let u0 = Level::zero();
        let one = Level::succ(Level::zero());
        let list_t = Expr::app(
            Expr::const_(Name::from_string("List"), vec![u0.clone()]),
            nat.clone(),
        );
        let list_nil_c = Expr::const_(Name::from_string("List.nil"), vec![u0.clone()]);
        let list_cons_c = Expr::const_(Name::from_string("List.cons"), vec![u0.clone()]);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let congr = Expr::const_(
            Name::from_string("congrArg"),
            vec![one.clone(), one.clone()],
        );
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let one_lit = Expr::nat_lit(1);

        let nil_e = Expr::app(list_nil_c.clone(), nat.clone()); // List.nil Nat
        let cons_e = |h: &Expr, t: &Expr| {
            Expr::apps(list_cons_c.clone(), [nat.clone(), h.clone(), t.clone()])
        };
        let eq_list = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [list_t.clone(), l, r]);
        let refl_list = |x: Expr| Expr::apps(eq_refl.clone(), [list_t.clone(), x]);
        // List.rec.{motive_lvl, 0} — args: [α, motive, nilMinor, consMinor, major]
        // consMinor : (h:α) → (t:List α) → motive t → motive (cons h t)
        let list_rec = |motive_lvl: Level| {
            Expr::const_(Name::from_string("List.rec"), vec![motive_lvl, u0.clone()])
        };
        // motive `λ _ : List Nat => List Nat` (for the map-style definitions).
        let const_list_motive = |b: &EnvDeclBuilder| {
            let mut c = EnvDeclBuilder::child_of(b);
            let (m_id, _m) = c.fresh_local(list_t.clone());
            c.finish_child(c.mk_lam(m_id, BinderInfo::Default, list_t.clone(), list_t.clone()))
        };

        // listSelf : List Nat → List Nat
        //   := λ l => List.rec.{1,0} Nat (λ _ => List Nat) nil (λ h t rec => cons h rec) l
        let list_self_val = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let motive = const_list_motive(&b);
            let cons_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat.clone());
                let (t_id, _t) = c.fresh_local(list_t.clone());
                let (r_id, r) = c.fresh_local(list_t.clone());
                let body = cons_e(&h, &r); // cons h rec
                let e = c.mk_lam(r_id, BinderInfo::Default, list_t.clone(), body);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let body = Expr::apps(
                list_rec(one.clone()),
                [nat.clone(), motive, nil_e.clone(), cons_minor, l.clone()],
            );
            b.finish(b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_LIST_SELF),
            level_params: vec![],
            type_: Expr::arrow(list_t.clone(), list_t.clone()),
            value: list_self_val,
            is_reducible: true,
        })?;
        let list_self = Expr::const_(Name::from_string(GIVEBACK_LIST_SELF), vec![]);
        let self_app = |x: &Expr| Expr::app(list_self.clone(), x.clone());

        // listIncr : List Nat → List Nat
        //   := λ l => List.rec.{1,0} Nat (λ _ => List Nat) nil (λ h t rec => cons (h+1) rec) l
        let incr_head = |h: &Expr| Expr::apps(nat_add.clone(), [h.clone(), one_lit.clone()]);
        let list_incr_val = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let motive = const_list_motive(&b);
            let cons_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat.clone());
                let (t_id, _t) = c.fresh_local(list_t.clone());
                let (r_id, r) = c.fresh_local(list_t.clone());
                let body = cons_e(&incr_head(&h), &r);
                let e = c.mk_lam(r_id, BinderInfo::Default, list_t.clone(), body);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let body = Expr::apps(
                list_rec(one.clone()),
                [nat.clone(), motive, nil_e.clone(), cons_minor, l.clone()],
            );
            b.finish(b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_LIST_INCR),
            level_params: vec![],
            type_: Expr::arrow(list_t.clone(), list_t.clone()),
            value: list_incr_val,
            is_reducible: true,
        })?;
        let list_incr = Expr::const_(Name::from_string(GIVEBACK_LIST_INCR), vec![]);

        // listSelf-cons : ∀ h t, listSelf (cons h t) = cons h (listSelf t)   (ι)
        let self_cons_type = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(nat.clone());
            let (t_id, t) = b.fresh_local(list_t.clone());
            let concl = eq_list(self_app(&cons_e(&h, &t)), cons_e(&h, &self_app(&t)));
            let e = b.mk_pi(t_id, BinderInfo::Default, list_t.clone(), concl);
            b.finish(b.mk_pi(h_id, BinderInfo::Default, nat.clone(), e))
        };
        let self_cons_val = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(nat.clone());
            let (t_id, t) = b.fresh_local(list_t.clone());
            let body = refl_list(cons_e(&h, &self_app(&t)));
            let e = b.mk_lam(t_id, BinderInfo::Default, list_t.clone(), body);
            b.finish(b.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LIST_SELF_CONS),
            level_params: vec![],
            type_: self_cons_type,
            value: self_cons_val,
        })?;

        // round-trip : ∀ l, listSelf l = l   (STRUCTURAL INDUCTION via List.rec)
        //   proof := λ l => List.rec.{0,0} Nat (λ ll => listSelf ll = ll)
        //              (Eq.refl … nil)
        //              (λ h t ih => congrArg (List Nat) (List Nat) (listSelf t) t
        //                             (λ x => cons h x) ih)
        //              l
        let roundtrip_type = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let concl = eq_list(self_app(&l), l.clone());
            b.finish(b.mk_pi(l_id, BinderInfo::Default, list_t.clone(), concl))
        };
        let roundtrip_val = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ll_id, ll) = c.fresh_local(list_t.clone());
                let body = eq_list(self_app(&ll), ll.clone());
                c.finish_child(c.mk_lam(ll_id, BinderInfo::Default, list_t.clone(), body))
            };
            let nil_proof = refl_list(nil_e.clone());
            let cons_proof = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat.clone());
                let (t_id, t) = c.fresh_local(list_t.clone());
                let ih_ty = eq_list(self_app(&t), t.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // f := λ x : List Nat => cons h x   (lifts the IH through `cons h`)
                let f = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, x) = d.fresh_local(list_t.clone());
                    d.finish_child(d.mk_lam(
                        x_id,
                        BinderInfo::Default,
                        list_t.clone(),
                        cons_e(&h, &x),
                    ))
                };
                // congrArg (List Nat) (List Nat) (listSelf t) t f ih
                //   : cons h (listSelf t) = cons h t   (def-eq to motive (cons h t))
                let body = Expr::apps(
                    congr.clone(),
                    [
                        list_t.clone(),
                        list_t.clone(),
                        self_app(&t),
                        t.clone(),
                        f,
                        ih.clone(),
                    ],
                );
                let e = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let body = Expr::apps(
                list_rec(Level::zero()),
                [nat.clone(), motive, nil_proof, cons_proof, l.clone()],
            );
            b.finish(b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LIST_ROUNDTRIP),
            level_params: vec![],
            type_: roundtrip_type,
            value: roundtrip_val,
        })?;

        // incr-cons : ∀ h t, listIncr (cons h t) = cons (h+1) (listIncr t)   (ι)
        let incr_cons_type = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(nat.clone());
            let (t_id, t) = b.fresh_local(list_t.clone());
            let rhs = cons_e(&incr_head(&h), &Expr::app(list_incr.clone(), t.clone()));
            let concl = eq_list(Expr::app(list_incr.clone(), cons_e(&h, &t)), rhs);
            let e = b.mk_pi(t_id, BinderInfo::Default, list_t.clone(), concl);
            b.finish(b.mk_pi(h_id, BinderInfo::Default, nat.clone(), e))
        };
        let incr_cons_val = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(nat.clone());
            let (t_id, t) = b.fresh_local(list_t.clone());
            let rhs = cons_e(&incr_head(&h), &Expr::app(list_incr.clone(), t.clone()));
            let e = b.mk_lam(t_id, BinderInfo::Default, list_t.clone(), refl_list(rhs));
            b.finish(b.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LIST_INCR_CONS),
            level_params: vec![],
            type_: incr_cons_type,
            value: incr_cons_val,
        })?;

        Ok(())
    }

    /// Build the **disjoint-mutable-borrows** anchor — the `split_at_mut`
    /// separation property. From one `(Nat, Nat)` pair Rust can hand out TWO
    /// simultaneous `&mut`s (`&mut p.0` and `&mut p.1`) precisely because they are
    /// DISJOINT. Each has its own backward function:
    ///
    ///   splitBack0 p v0 := Prod.mk v0 p.snd     (give back through `&mut p.0`)
    ///   splitBack1 p v1 := Prod.mk p.fst v1     (give back through `&mut p.1`)
    ///
    /// Proves (axiom-clean, by projection-ι + structure-eta + `Eq.refl`):
    ///
    ///   * disjoint01 `(splitBack0 p v0).snd = p.snd`   (borrow 0 cannot touch p.1)
    ///   * disjoint10 `(splitBack1 p v1).fst = p.fst`   (borrow 1 cannot touch p.0)
    ///   * **commute** `splitBack1 (splitBack0 p v0) v1 = splitBack0 (splitBack1 p v1) v0`
    ///     — the two give-backs COMMUTE, so the order of recombination is
    ///     irrelevant: the soundness witness for aliasing-XOR-mutation.
    ///   * combine  `splitBack1 (splitBack0 p v0) v1 = Prod.mk v0 v1`
    ///
    /// commute is the separation law a skeptic checks for `split_at_mut`: two live
    /// `&mut`s into one value are sound exactly when their give-backs don't interfere.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Prod`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_split_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_prod()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Level::zero();
        let prod_lv = vec![zero.clone(), zero.clone()];
        let one = Level::succ(Level::zero());
        let pair_t = Expr::apps(
            Expr::const_(Name::from_string("Prod"), prod_lv.clone()),
            [nat.clone(), nat.clone()],
        );
        let prod_mk = Expr::const_(Name::from_string("Prod.mk"), prod_lv.clone());
        let prod_fst = Expr::const_(Name::from_string("Prod.fst"), prod_lv.clone());
        let prod_snd = Expr::const_(Name::from_string("Prod.snd"), prod_lv);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

        let mk = |a: &Expr, b: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [nat.clone(), nat.clone(), a.clone(), b.clone()],
            )
        };
        let fst = |p: &Expr| Expr::apps(prod_fst.clone(), [nat.clone(), nat.clone(), p.clone()]);
        let snd = |p: &Expr| Expr::apps(prod_snd.clone(), [nat.clone(), nat.clone(), p.clone()]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);
        let eq_pair = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [pair_t.clone(), l, r]);
        let refl_nat = |x: Expr| Expr::apps(eq_refl.clone(), [nat.clone(), x]);
        let refl_pair = |x: Expr| Expr::apps(eq_refl.clone(), [pair_t.clone(), x]);

        // splitBack0 p v0 := Prod.mk v0 p.snd
        let back0_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let body = mk(&v, &snd(&p));
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_SPLIT_BACK0),
            level_params: vec![],
            type_: Expr::arrow(pair_t.clone(), Expr::arrow(nat.clone(), pair_t.clone())),
            value: back0_val,
            is_reducible: true,
        })?;
        let back0 = Expr::const_(Name::from_string(GIVEBACK_SPLIT_BACK0), vec![]);

        // splitBack1 p v1 := Prod.mk p.fst v1
        let back1_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let body = mk(&fst(&p), &v);
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_SPLIT_BACK1),
            level_params: vec![],
            type_: Expr::arrow(pair_t.clone(), Expr::arrow(nat.clone(), pair_t.clone())),
            value: back1_val,
            is_reducible: true,
        })?;
        let back1 = Expr::const_(Name::from_string(GIVEBACK_SPLIT_BACK1), vec![]);
        let b0 = |p: &Expr, v: &Expr| Expr::apps(back0.clone(), [p.clone(), v.clone()]);
        let b1 = |p: &Expr, v: &Expr| Expr::apps(back1.clone(), [p.clone(), v.clone()]);

        // disjoint01 : ∀ p v0, (splitBack0 p v0).snd = p.snd
        let disj01_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(snd(&b0(&p, &v)), snd(&p));
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let disj01_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, _v) = b.fresh_local(nat.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), refl_nat(snd(&p)));
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_SPLIT_DISJOINT01),
            level_params: vec![],
            type_: disj01_type,
            value: disj01_val,
        })?;

        // disjoint10 : ∀ p v1, (splitBack1 p v1).fst = p.fst
        let disj10_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(fst(&b1(&p, &v)), fst(&p));
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let disj10_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v_id, _v) = b.fresh_local(nat.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), refl_nat(fst(&p)));
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_SPLIT_DISJOINT10),
            level_params: vec![],
            type_: disj10_type,
            value: disj10_val,
        })?;

        // commute : ∀ p v0 v1, splitBack1 (splitBack0 p v0) v1 = splitBack0 (splitBack1 p v1) v0
        //   both sides reduce (proj-ι) to Prod.mk v0 v1.
        let commute_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v0_id, v0) = b.fresh_local(nat.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let concl = eq_pair(b1(&b0(&p, &v0), &v1), b0(&b1(&p, &v1), &v0));
            let e = b.mk_pi(v1_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(v0_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let commute_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _p) = b.fresh_local(pair_t.clone());
            let (v0_id, v0) = b.fresh_local(nat.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let body = refl_pair(mk(&v0, &v1));
            let e = b.mk_lam(v1_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(v0_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_SPLIT_COMMUTE),
            level_params: vec![],
            type_: commute_type,
            value: commute_val,
        })?;

        // combine : ∀ p v0 v1, splitBack1 (splitBack0 p v0) v1 = Prod.mk v0 v1
        let combine_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pair_t.clone());
            let (v0_id, v0) = b.fresh_local(nat.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let concl = eq_pair(b1(&b0(&p, &v0), &v1), mk(&v0, &v1));
            let e = b.mk_pi(v1_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(v0_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let combine_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _p) = b.fresh_local(pair_t.clone());
            let (v0_id, v0) = b.fresh_local(nat.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let body = refl_pair(mk(&v0, &v1));
            let e = b.mk_lam(v1_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(v0_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_SPLIT_COMBINE),
            level_params: vec![],
            type_: combine_type,
            value: combine_val,
        })?;

        Ok(())
    }

    /// Build the **control-flow give-back** anchor — the give-back of a CONDITIONAL
    /// mutation `if c { *x = v }`. The backward function branches on the same
    /// runtime flag the forward did (`Bool.rec`):
    ///
    ///   condSet c old v := if c then v else old
    ///
    /// Proves (axiom-clean): the two per-branch laws by ι (`condSet true old v = v`,
    /// `condSet false old v = old` — the false branch FRAMES the value), and the
    /// `∀ c` law `condSet c old old = old` (setting to the current value is a no-op
    /// on EITHER branch), proved by `Bool.rec` CASE ANALYSIS over the opaque flag.
    /// This is the control-flow tier: give-back through branches, the case a
    /// skeptic checks once straight-line code works.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Bool`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_cond_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_bool()?; // Bool, Bool.true/false, Bool.rec
        self.init_prod()?; // Prod (for the Prod-typed conditional combinator)

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let one = Level::succ(Level::zero());
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);
        let refl_nat = |x: Expr| Expr::apps(eq_refl.clone(), [nat.clone(), x]);
        // Bool.rec.{motive_lvl} — args: [motive, falseMinor, trueMinor, major]
        let bool_rec =
            |motive_lvl: Level| Expr::const_(Name::from_string("Bool.rec"), vec![motive_lvl]);

        // condSet : Bool → Nat → Nat → Nat
        //   := λ c old v => Bool.rec.{1} (λ _:Bool => Nat) old v c   (false→old, true→v)
        let cond_set_val = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(bool_c.clone());
            let (old_id, old) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = d.fresh_local(bool_c.clone());
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, bool_c.clone(), nat.clone()))
            };
            let body = Expr::apps(
                bool_rec(one.clone()),
                [motive, old.clone(), v.clone(), c.clone()],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(old_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(c_id, BinderInfo::Default, bool_c.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_COND_SET),
            level_params: vec![],
            type_: Expr::arrow(
                bool_c.clone(),
                Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
            ),
            value: cond_set_val,
            is_reducible: true,
        })?;
        let cond_set = Expr::const_(Name::from_string(GIVEBACK_COND_SET), vec![]);
        let cset = |c: &Expr, old: &Expr, v: &Expr| {
            Expr::apps(cond_set.clone(), [c.clone(), old.clone(), v.clone()])
        };

        // cond_true : ∀ old v, condSet true old v = v   (ι)
        let true_type = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, old) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(cset(&btrue, &old, &v), v.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(old_id, BinderInfo::Default, nat.clone(), e))
        };
        let true_val = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, _old) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), refl_nat(v));
            b.finish(b.mk_lam(old_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_COND_TRUE),
            level_params: vec![],
            type_: true_type,
            value: true_val,
        })?;

        // cond_false : ∀ old v, condSet false old v = old   (ι; the false branch frames)
        let false_type = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, old) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(cset(&bfalse, &old, &v), old.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(old_id, BinderInfo::Default, nat.clone(), e))
        };
        let false_val = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, old) = b.fresh_local(nat.clone());
            let (v_id, _v) = b.fresh_local(nat.clone());
            let e = b.mk_lam(
                v_id,
                BinderInfo::Default,
                nat.clone(),
                refl_nat(old.clone()),
            );
            b.finish(b.mk_lam(old_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_COND_FALSE),
            level_params: vec![],
            type_: false_type,
            value: false_val,
        })?;

        // cond_self : ∀ c old, condSet c old old = old   (∀c by Bool.rec case analysis)
        //   proof := λ c old => Bool.rec.{0} (λ cc => condSet cc old old = old)
        //              (Eq.refl … old)   -- false branch
        //              (Eq.refl … old)   -- true branch (true→v=old)
        //              c
        let self_type = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(bool_c.clone());
            let (old_id, old) = b.fresh_local(nat.clone());
            let concl = eq_nat(cset(&c, &old, &old), old.clone());
            let e = b.mk_pi(old_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(c_id, BinderInfo::Default, bool_c.clone(), e))
        };
        let self_val = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(bool_c.clone());
            let (old_id, old) = b.fresh_local(nat.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (cc_id, cc) = d.fresh_local(bool_c.clone());
                let body = eq_nat(cset(&cc, &old, &old), old.clone());
                d.finish_child(d.mk_lam(cc_id, BinderInfo::Default, bool_c.clone(), body))
            };
            let body = Expr::apps(
                bool_rec(Level::zero()),
                [
                    motive,
                    refl_nat(old.clone()),
                    refl_nat(old.clone()),
                    c.clone(),
                ],
            );
            let e = b.mk_lam(old_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(c_id, BinderInfo::Default, bool_c.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_COND_SELF),
            level_params: vec![],
            type_: self_type,
            value: self_val,
        })?;

        // ── Prod-typed conditional give-back (COMPOSITION: the conditional over an
        //    AGGREGATE place, e.g. `if c { p.0 += 1 }` over `&mut (Nat, Nat)`). The
        //    place value is a pair, so the combinator is over `Prod Nat Nat`. Because
        //    `Prod Nat Nat : Sort 1` (exactly like `Nat`), the SAME `Bool.rec.{1}` /
        //    `Eq.{1}` levels carry over — no universe polymorphism needed.
        let prod = Expr::const_(
            Name::from_string("Prod"),
            vec![Level::zero(), Level::zero()],
        );
        let pair_t = Expr::apps(prod, [nat.clone(), nat.clone()]);
        let eq_pair = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [pair_t.clone(), l, r]);
        let refl_pair = |x: Expr| Expr::apps(eq_refl.clone(), [pair_t.clone(), x]);

        // condSetPair : Bool → (Prod Nat Nat) → (Prod Nat Nat) → (Prod Nat Nat)
        //   := λ c old v => Bool.rec.{1} (λ _:Bool => Prod Nat Nat) old v c
        let cond_set_pair_val = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(bool_c.clone());
            let (old_id, old) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(pair_t.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = d.fresh_local(bool_c.clone());
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, bool_c.clone(), pair_t.clone()))
            };
            let body = Expr::apps(
                bool_rec(one.clone()),
                [motive, old.clone(), v.clone(), c.clone()],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, pair_t.clone(), body);
            let e = b.mk_lam(old_id, BinderInfo::Default, pair_t.clone(), e);
            b.finish(b.mk_lam(c_id, BinderInfo::Default, bool_c.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_COND_SET_PAIR),
            level_params: vec![],
            type_: Expr::arrow(
                bool_c.clone(),
                Expr::arrow(pair_t.clone(), Expr::arrow(pair_t.clone(), pair_t.clone())),
            ),
            value: cond_set_pair_val,
            is_reducible: true,
        })?;
        let cond_set_pair = Expr::const_(Name::from_string(GIVEBACK_COND_SET_PAIR), vec![]);
        let csetp = |c: &Expr, old: &Expr, v: &Expr| {
            Expr::apps(cond_set_pair.clone(), [c.clone(), old.clone(), v.clone()])
        };

        // condPair_true : ∀ old v, condSetPair true old v = v   (ι)
        let ptrue_type = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, old) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(pair_t.clone());
            let concl = eq_pair(csetp(&btrue, &old, &v), v.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, pair_t.clone(), concl);
            b.finish(b.mk_pi(old_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let ptrue_val = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, _old) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(pair_t.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, pair_t.clone(), refl_pair(v));
            b.finish(b.mk_lam(old_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_COND_PAIR_TRUE),
            level_params: vec![],
            type_: ptrue_type,
            value: ptrue_val,
        })?;

        // condPair_false : ∀ old v, condSetPair false old v = old   (ι; the frame branch)
        let pfalse_type = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, old) = b.fresh_local(pair_t.clone());
            let (v_id, v) = b.fresh_local(pair_t.clone());
            let concl = eq_pair(csetp(&bfalse, &old, &v), old.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, pair_t.clone(), concl);
            b.finish(b.mk_pi(old_id, BinderInfo::Default, pair_t.clone(), e))
        };
        let pfalse_val = {
            let mut b = EnvDeclBuilder::new();
            let (old_id, old) = b.fresh_local(pair_t.clone());
            let (v_id, _v) = b.fresh_local(pair_t.clone());
            let e = b.mk_lam(
                v_id,
                BinderInfo::Default,
                pair_t.clone(),
                refl_pair(old.clone()),
            );
            b.finish(b.mk_lam(old_id, BinderInfo::Default, pair_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_COND_PAIR_FALSE),
            level_params: vec![],
            type_: pfalse_type,
            value: pfalse_val,
        })?;

        // ── Universe-POLYMORPHIC conditional give-back (the ANTI-CATALOG primitive):
        //    ONE combinator + two laws that work for ANY place type α, subsuming the
        //    Nat and Prod-Nat-Nat versions and every future place type. α : Type u =
        //    Sort (u+1), so the motive `λ_:Bool => α` lives in Sort (u+1) ⇒ Bool.rec.{u+1}
        //    and the Eq over α-values is Eq.{u+1}.
        let u_name = Name::from_string("u");
        let u_lvl = Level::param(u_name.clone());
        let type_u = Expr::sort(Level::succ(u_lvl.clone())); // Type u
        let rec_u = Level::succ(u_lvl.clone()); // motive / Eq level = u+1
        let eqc_u = Expr::const_(Name::from_string("Eq"), vec![rec_u.clone()]);
        let eq_refl_u = Expr::const_(Name::from_string("Eq.refl"), vec![rec_u.clone()]);
        let cond_set_p =
            |lvl: Level| Expr::const_(Name::from_string(GIVEBACK_COND_SET_POLY), vec![lvl]);

        // condSetP.{u} : {α : Type u} → Bool → α → α → α
        //   := λ {α} c old v => Bool.rec.{u+1} (λ _:Bool => α) old v c
        let cond_set_p_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let e = Expr::arrow(
                bool_c.clone(),
                Expr::arrow(a.clone(), Expr::arrow(a.clone(), a.clone())),
            );
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let cond_set_p_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (c_id, c) = b.fresh_local(bool_c.clone());
            let (old_id, old) = b.fresh_local(a.clone());
            let (v_id, v) = b.fresh_local(a.clone());
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = d.fresh_local(bool_c.clone());
                d.finish_child(d.mk_lam(m_id, BinderInfo::Default, bool_c.clone(), a.clone()))
            };
            let body = Expr::apps(
                bool_rec(rec_u.clone()),
                [motive, old.clone(), v.clone(), c.clone()],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, a.clone(), body);
            let e = b.mk_lam(old_id, BinderInfo::Default, a.clone(), e);
            let e = b.mk_lam(c_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_COND_SET_POLY),
            level_params: vec![u_name.clone()],
            type_: cond_set_p_type,
            value: cond_set_p_val,
            is_reducible: true,
        })?;

        // condSetP_true.{u} : {α : Type u} → ∀ old v, condSetP true old v = v   (ι)
        let poly_true_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (old_id, old) = b.fresh_local(a.clone());
            let (v_id, v) = b.fresh_local(a.clone());
            let lhs = Expr::apps(
                cond_set_p(u_lvl.clone()),
                [a.clone(), btrue.clone(), old.clone(), v.clone()],
            );
            let concl = Expr::apps(eqc_u.clone(), [a.clone(), lhs, v.clone()]);
            let e = b.mk_pi(v_id, BinderInfo::Default, a.clone(), concl);
            let e = b.mk_pi(old_id, BinderInfo::Default, a.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let poly_true_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (old_id, _old) = b.fresh_local(a.clone());
            let (v_id, v) = b.fresh_local(a.clone());
            let refl = Expr::apps(eq_refl_u.clone(), [a.clone(), v.clone()]);
            let e = b.mk_lam(v_id, BinderInfo::Default, a.clone(), refl);
            let e = b.mk_lam(old_id, BinderInfo::Default, a.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_COND_POLY_TRUE),
            level_params: vec![u_name.clone()],
            type_: poly_true_type,
            value: poly_true_val,
        })?;

        // condSetP_false.{u} : {α : Type u} → ∀ old v, condSetP false old v = old  (ι)
        let poly_false_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (old_id, old) = b.fresh_local(a.clone());
            let (v_id, v) = b.fresh_local(a.clone());
            let lhs = Expr::apps(
                cond_set_p(u_lvl.clone()),
                [a.clone(), bfalse.clone(), old.clone(), v.clone()],
            );
            let concl = Expr::apps(eqc_u.clone(), [a.clone(), lhs, old.clone()]);
            let e = b.mk_pi(v_id, BinderInfo::Default, a.clone(), concl);
            let e = b.mk_pi(old_id, BinderInfo::Default, a.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let poly_false_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (old_id, old) = b.fresh_local(a.clone());
            let (v_id, _v) = b.fresh_local(a.clone());
            let refl = Expr::apps(eq_refl_u.clone(), [a.clone(), old.clone()]);
            let e = b.mk_lam(v_id, BinderInfo::Default, a.clone(), refl);
            let e = b.mk_lam(old_id, BinderInfo::Default, a.clone(), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_COND_POLY_FALSE),
            level_params: vec![u_name],
            type_: poly_false_type,
            value: poly_false_val,
        })?;

        Ok(())
    }

    /// Build the **nested give-back** anchor — a `&mut` into a field NESTED two
    /// levels deep (`&mut p.0.0` over `((Nat, Nat), Nat)`; the data-nesting analog
    /// of a `&mut &mut T` reborrow). The backward function must rebuild BOTH levels
    /// and frame the sibling at EACH level:
    ///
    ///   nestFwd  p    := (p.fst).fst
    ///   nestBack p v' := Prod.mk (Prod.mk v' (p.fst).snd) p.snd
    ///
    /// Proves (axiom-clean): put-get (ι×2), frame-inner (`p.0.1` untouched),
    /// frame-outer (`p.1` untouched), and the **nested round-trip**
    /// `nestBack p (nestFwd p) = p`, which requires the kernel's structure-eta to
    /// fire at BOTH nesting levels (inner `Prod.mk p.0.0 p.0.1 = p.0`, then outer
    /// `Prod.mk p.0 p.1 = p`). The deep round-trip is the law a skeptic checks for
    /// nested data / reborrows.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Prod`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_nested_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_prod()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Level::zero();
        let lv = vec![zero.clone(), zero.clone()];
        let one = Level::succ(Level::zero());
        let prod = Expr::const_(Name::from_string("Prod"), lv.clone());
        let prod_mk = Expr::const_(Name::from_string("Prod.mk"), lv.clone());
        let prod_fst = Expr::const_(Name::from_string("Prod.fst"), lv.clone());
        let prod_snd = Expr::const_(Name::from_string("Prod.snd"), lv);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

        let inner_t = Expr::apps(prod.clone(), [nat.clone(), nat.clone()]); // Prod Nat Nat
        let outer_t = Expr::apps(prod.clone(), [inner_t.clone(), nat.clone()]); // Prod (Prod Nat Nat) Nat
                                                                                // Inner pair ops (over Nat, Nat).
        let mk_i = |a: &Expr, b: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [nat.clone(), nat.clone(), a.clone(), b.clone()],
            )
        };
        let fst_i = |i: &Expr| Expr::apps(prod_fst.clone(), [nat.clone(), nat.clone(), i.clone()]);
        let snd_i = |i: &Expr| Expr::apps(prod_snd.clone(), [nat.clone(), nat.clone(), i.clone()]);
        // Outer pair ops (over Inner, Nat).
        let mk_o = |a: &Expr, b: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [inner_t.clone(), nat.clone(), a.clone(), b.clone()],
            )
        };
        let fst_o =
            |p: &Expr| Expr::apps(prod_fst.clone(), [inner_t.clone(), nat.clone(), p.clone()]);
        let snd_o =
            |p: &Expr| Expr::apps(prod_snd.clone(), [inner_t.clone(), nat.clone(), p.clone()]);

        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);
        let eq_outer = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [outer_t.clone(), l, r]);
        let refl_nat = |x: Expr| Expr::apps(eq_refl.clone(), [nat.clone(), x]);
        let refl_outer = |x: Expr| Expr::apps(eq_refl.clone(), [outer_t.clone(), x]);

        // nestFwd : Outer → Nat := λ p => (p.fst).fst
        let fwd_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let body = fst_i(&fst_o(&p));
            b.finish(b.mk_lam(p_id, BinderInfo::Default, outer_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_NEST_FWD),
            level_params: vec![],
            type_: Expr::arrow(outer_t.clone(), nat.clone()),
            value: fwd_val,
            is_reducible: true,
        })?;
        let nest_fwd = Expr::const_(Name::from_string(GIVEBACK_NEST_FWD), vec![]);

        // nestBack : Outer → Nat → Outer
        //   := λ p v => Prod.mk (Prod.mk v (p.fst).snd) p.snd
        let back_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let new_inner = mk_i(&v, &snd_i(&fst_o(&p)));
            let body = mk_o(&new_inner, &snd_o(&p));
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, outer_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_NEST_BACK),
            level_params: vec![],
            type_: Expr::arrow(outer_t.clone(), Expr::arrow(nat.clone(), outer_t.clone())),
            value: back_val,
            is_reducible: true,
        })?;
        let nest_back = Expr::const_(Name::from_string(GIVEBACK_NEST_BACK), vec![]);
        let fwd = |p: &Expr| Expr::app(nest_fwd.clone(), p.clone());
        let back = |p: &Expr, v: &Expr| Expr::apps(nest_back.clone(), [p.clone(), v.clone()]);

        // put-get : ∀ p v, nestFwd (nestBack p v) = v   (ι×2)
        let pg_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(fwd(&back(&p, &v)), v.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, outer_t.clone(), e))
        };
        let pg_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, _p) = b.fresh_local(outer_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), refl_nat(v));
            b.finish(b.mk_lam(p_id, BinderInfo::Default, outer_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_NEST_PUT_GET),
            level_params: vec![],
            type_: pg_type,
            value: pg_val,
        })?;

        // get-put : ∀ p, nestBack p (nestFwd p) = p   (structure-eta at BOTH levels)
        let gp_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let concl = eq_outer(back(&p, &fwd(&p)), p.clone());
            b.finish(b.mk_pi(p_id, BinderInfo::Default, outer_t.clone(), concl))
        };
        let gp_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            b.finish(b.mk_lam(p_id, BinderInfo::Default, outer_t.clone(), refl_outer(p)))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_NEST_GET_PUT),
            level_params: vec![],
            type_: gp_type,
            value: gp_val,
        })?;

        // frame-inner : ∀ p v, (nestBack p v).fst.snd = p.fst.snd
        let fi_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(snd_i(&fst_o(&back(&p, &v))), snd_i(&fst_o(&p)));
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, outer_t.clone(), e))
        };
        let fi_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let (v_id, _v) = b.fresh_local(nat.clone());
            let body = refl_nat(snd_i(&fst_o(&p)));
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, outer_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_NEST_FRAME_INNER),
            level_params: vec![],
            type_: fi_type,
            value: fi_val,
        })?;

        // frame-outer : ∀ p v, (nestBack p v).snd = p.snd
        let fo_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(snd_o(&back(&p, &v)), snd_o(&p));
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Default, outer_t.clone(), e))
        };
        let fo_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let (v_id, _v) = b.fresh_local(nat.clone());
            let body = refl_nat(snd_o(&p));
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, outer_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_NEST_FRAME_OUTER),
            level_params: vec![],
            type_: fo_type,
            value: fo_val,
        })?;

        // incr : ∀ p, nestFwd (nestBack p (nestFwd p + 1)) = nestFwd p + 1
        // The give-back of a doubly-nested field increment `p.0.0 += 1`: after giving
        // back the incremented deep field, reading it back yields incr(old deep field)
        // — and by frame-inner/frame-outer BOTH siblings (p.0.1, p.1) are untouched.
        // `nestFwd ∘ nestBack` reduces to the identity by projection-ι at BOTH nesting
        // levels (δ over the reducible defs), so both sides whnf to `nestFwd p + 1` and
        // `Eq.refl` closes it — the nested analog of `aggFst_incr`.
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let one_lit = Expr::nat_lit(1);
        let incr = |p: &Expr| Expr::apps(nat_add.clone(), [fwd(p), one_lit.clone()]);
        let incr_type = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            let concl = eq_nat(fwd(&back(&p, &incr(&p))), incr(&p));
            b.finish(b.mk_pi(p_id, BinderInfo::Default, outer_t.clone(), concl))
        };
        let incr_val = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(outer_t.clone());
            b.finish(b.mk_lam(
                p_id,
                BinderInfo::Default,
                outer_t.clone(),
                refl_nat(incr(&p)),
            ))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_NEST_INCR),
            level_params: vec![],
            type_: incr_type,
            value: incr_val,
        })?;

        Ok(())
    }

    /// Build the **loop give-back** anchor — Aeneas's signature loop backward
    /// functions. Models `for x in &mut l { *x += 1 }`: the loop FORWARD maps `+1`
    /// over the whole list, and its BACKWARD function maps `pred` (undoes one
    /// increment per element). Both by `List.rec`. Proves (axiom-clean):
    ///
    ///   * loopFwd-cons `loopFwd (cons h t) = cons (h+1) (loopFwd t)`   (one iter, ι)
    ///   * **round-trip** `∀ l, loopBack (loopFwd l) = l`   (STRUCTURAL INDUCTION:
    ///     per element `Nat.pred (Nat.add h 1) = h` by ι, lifted through the spine
    ///     via the recursion hypothesis + `congrArg`)
    ///
    /// The round-trip is Aeneas's loop-give-back property: the loop's backward
    /// function inverts its forward over the ENTIRE list, however long. This is the
    /// loop tier a skeptic checks — give-back through iteration, proved once for all
    /// list lengths by induction, not unrolled.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `List`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_loop_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?; // also brings Nat.pred, Nat.add
        self.init_eq()?; // registers congrArg
        self.init_list()?;
        self.init_bool()?; // Bool, Bool.not, Bool.rec (for the boolean-flip loop instance)
        self.init_prod()?; // Prod, Prod.mk/fst/snd (for the pair-field-increment loop)

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let u0 = Level::zero();
        let one = Level::succ(Level::zero());
        let list_t = Expr::app(
            Expr::const_(Name::from_string("List"), vec![u0.clone()]),
            nat.clone(),
        );
        let list_nil_c = Expr::const_(Name::from_string("List.nil"), vec![u0.clone()]);
        let list_cons_c = Expr::const_(Name::from_string("List.cons"), vec![u0.clone()]);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let congr = Expr::const_(
            Name::from_string("congrArg"),
            vec![one.clone(), one.clone()],
        );
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_pred = Expr::const_(Name::from_string("Nat.pred"), vec![]);
        let one_lit = Expr::nat_lit(1);

        let nil_e = Expr::app(list_nil_c.clone(), nat.clone());
        let cons_e = |h: &Expr, t: &Expr| {
            Expr::apps(list_cons_c.clone(), [nat.clone(), h.clone(), t.clone()])
        };
        let eq_list = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [list_t.clone(), l, r]);
        let refl_list = |x: Expr| Expr::apps(eq_refl.clone(), [list_t.clone(), x]);
        let list_rec = |motive_lvl: Level| {
            Expr::const_(Name::from_string("List.rec"), vec![motive_lvl, u0.clone()])
        };
        let const_list_motive = |b: &EnvDeclBuilder| {
            let mut c = EnvDeclBuilder::child_of(b);
            let (m_id, _m) = c.fresh_local(list_t.clone());
            c.finish_child(c.mk_lam(m_id, BinderInfo::Default, list_t.clone(), list_t.clone()))
        };
        let succ_h = |h: &Expr| Expr::apps(nat_add.clone(), [h.clone(), one_lit.clone()]);
        let pred_h = |h: &Expr| Expr::app(nat_pred.clone(), h.clone());

        // A map over the list: λ l => List.rec.{1,0} Nat (λ_=>List Nat) nil
        //   (λ h t rec => cons (f h) rec) l   — f applied to the head, recurse on tail.
        let mut declare_map = |name: &str, f: &dyn Fn(&Expr) -> Expr| -> Result<(), EnvError> {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (l_id, l) = b.fresh_local(list_t.clone());
                let motive = const_list_motive(&b);
                let cons_minor = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (h_id, h) = c.fresh_local(nat.clone());
                    let (t_id, _t) = c.fresh_local(list_t.clone());
                    let (r_id, r) = c.fresh_local(list_t.clone());
                    let body = cons_e(&f(&h), &r);
                    let e = c.mk_lam(r_id, BinderInfo::Default, list_t.clone(), body);
                    let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                    c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
                };
                let body = Expr::apps(
                    list_rec(one.clone()),
                    [nat.clone(), motive, nil_e.clone(), cons_minor, l.clone()],
                );
                b.finish(b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), body))
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::arrow(list_t.clone(), list_t.clone()),
                value: val,
                is_reducible: true,
            })
        };
        declare_map(GIVEBACK_LOOP_FWD, &succ_h)?;
        declare_map(GIVEBACK_LOOP_BACK, &pred_h)?;
        let loop_fwd = Expr::const_(Name::from_string(GIVEBACK_LOOP_FWD), vec![]);
        let loop_back = Expr::const_(Name::from_string(GIVEBACK_LOOP_BACK), vec![]);
        let lf = |x: &Expr| Expr::app(loop_fwd.clone(), x.clone());
        let lb = |x: &Expr| Expr::app(loop_back.clone(), x.clone());

        // loopFwd-cons : ∀ h t, loopFwd (cons h t) = cons (h+1) (loopFwd t)   (ι)
        let fc_type = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(nat.clone());
            let (t_id, t) = b.fresh_local(list_t.clone());
            let concl = eq_list(lf(&cons_e(&h, &t)), cons_e(&succ_h(&h), &lf(&t)));
            let e = b.mk_pi(t_id, BinderInfo::Default, list_t.clone(), concl);
            b.finish(b.mk_pi(h_id, BinderInfo::Default, nat.clone(), e))
        };
        let fc_val = {
            let mut b = EnvDeclBuilder::new();
            let (h_id, h) = b.fresh_local(nat.clone());
            let (t_id, t) = b.fresh_local(list_t.clone());
            let body = refl_list(cons_e(&succ_h(&h), &lf(&t)));
            let e = b.mk_lam(t_id, BinderInfo::Default, list_t.clone(), body);
            b.finish(b.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LOOP_FWD_CONS),
            level_params: vec![],
            type_: fc_type,
            value: fc_val,
        })?;

        // round-trip : ∀ l, loopBack (loopFwd l) = l   (STRUCTURAL INDUCTION)
        let rt_type = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let concl = eq_list(lb(&lf(&l)), l.clone());
            b.finish(b.mk_pi(l_id, BinderInfo::Default, list_t.clone(), concl))
        };
        let rt_val = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ll_id, ll) = c.fresh_local(list_t.clone());
                let body = eq_list(lb(&lf(&ll)), ll.clone());
                c.finish_child(c.mk_lam(ll_id, BinderInfo::Default, list_t.clone(), body))
            };
            let nil_proof = refl_list(nil_e.clone());
            let cons_proof = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat.clone());
                let (t_id, t) = c.fresh_local(list_t.clone());
                let ih_ty = eq_list(lb(&lf(&t)), t.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // f := λ x : List Nat => cons h x   (lifts the IH; head is def-eq h
                // because pred(h+1) ι-reduces to h).
                let f = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, x) = d.fresh_local(list_t.clone());
                    d.finish_child(d.mk_lam(
                        x_id,
                        BinderInfo::Default,
                        list_t.clone(),
                        cons_e(&h, &x),
                    ))
                };
                let body = Expr::apps(
                    congr.clone(),
                    [
                        list_t.clone(),
                        list_t.clone(),
                        lb(&lf(&t)),
                        t.clone(),
                        f,
                        ih.clone(),
                    ],
                );
                let e = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let body = Expr::apps(
                list_rec(Level::zero()),
                [nat.clone(), motive, nil_proof, cons_proof, l.clone()],
            );
            b.finish(b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LOOP_ROUNDTRIP),
            level_params: vec![],
            type_: rt_type,
            value: rt_val,
        })?;

        // ── THE GENERAL loop give-back: for ANY element function f with a left inverse
        //    finv, `listMap finv (listMap f l) = l`. Arbitrary-body loop, not just +1.
        let nat_to_nat = Expr::arrow(nat.clone(), nat.clone());
        let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]);

        // listMap : (Nat → Nat) → List Nat → List Nat
        //   := λ g l => List.rec.{1,0} Nat (λ_=>List Nat) nil (λ h t rec => cons (g h) rec) l
        let list_map_val = {
            let mut b = EnvDeclBuilder::new();
            let (g_id, g) = b.fresh_local(nat_to_nat.clone());
            let (l_id, l) = b.fresh_local(list_t.clone());
            let motive = const_list_motive(&b);
            let cons_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat.clone());
                let (t_id, _t) = c.fresh_local(list_t.clone());
                let (r_id, r) = c.fresh_local(list_t.clone());
                let body = cons_e(&Expr::app(g.clone(), h.clone()), &r);
                let e = c.mk_lam(r_id, BinderInfo::Default, list_t.clone(), body);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let rec = Expr::apps(
                list_rec(one.clone()),
                [nat.clone(), motive, nil_e.clone(), cons_minor, l.clone()],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), rec);
            b.finish(b.mk_lam(g_id, BinderInfo::Default, nat_to_nat.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_LOOP_MAP),
            level_params: vec![],
            type_: Expr::arrow(
                nat_to_nat.clone(),
                Expr::arrow(list_t.clone(), list_t.clone()),
            ),
            value: list_map_val,
            is_reducible: true,
        })?;
        let list_map = Expr::const_(Name::from_string(GIVEBACK_LOOP_MAP), vec![]);
        let map_app = |g: &Expr, l: &Expr| Expr::apps(list_map.clone(), [g.clone(), l.clone()]);

        // listMap_roundTrip : ∀ (f finv : Nat→Nat), (∀ x, finv (f x) = x) →
        //                       ∀ l, listMap finv (listMap f l) = l
        let eq_nat = |a: Expr, bb: Expr| Expr::apps(eqc.clone(), [nat.clone(), a, bb]);
        let mrt_type = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(nat_to_nat.clone());
            let (fi_id, fi) = b.fresh_local(nat_to_nat.clone());
            // hinv : ∀ x, finv (f x) = x
            let hinv_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(nat.clone());
                let concl = eq_nat(
                    Expr::app(fi.clone(), Expr::app(f.clone(), x.clone())),
                    x.clone(),
                );
                c.finish_child(c.mk_pi(x_id, BinderInfo::Default, nat.clone(), concl))
            };
            let (hinv_id, _hinv) = b.fresh_local(hinv_ty.clone());
            let (l_id, l) = b.fresh_local(list_t.clone());
            let concl = eq_list(map_app(&fi, &map_app(&f, &l)), l.clone());
            let e = b.mk_pi(l_id, BinderInfo::Default, list_t.clone(), concl);
            let e = b.mk_pi(hinv_id, BinderInfo::Default, hinv_ty, e);
            let e = b.mk_pi(fi_id, BinderInfo::Default, nat_to_nat.clone(), e);
            b.finish(b.mk_pi(f_id, BinderInfo::Default, nat_to_nat.clone(), e))
        };
        let mrt_val = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(nat_to_nat.clone());
            let (fi_id, fi) = b.fresh_local(nat_to_nat.clone());
            let hinv_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(nat.clone());
                let concl = eq_nat(
                    Expr::app(fi.clone(), Expr::app(f.clone(), x.clone())),
                    x.clone(),
                );
                c.finish_child(c.mk_pi(x_id, BinderInfo::Default, nat.clone(), concl))
            };
            let (hinv_id, hinv) = b.fresh_local(hinv_ty.clone());
            let (l_id, l) = b.fresh_local(list_t.clone());
            // motive : λ ll => listMap finv (listMap f ll) = ll
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ll_id, ll) = c.fresh_local(list_t.clone());
                let body = eq_list(map_app(&fi, &map_app(&f, &ll)), ll.clone());
                c.finish_child(c.mk_lam(ll_id, BinderInfo::Default, list_t.clone(), body))
            };
            let nil_proof = refl_list(nil_e.clone());
            let cons_proof = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat.clone());
                let (t_id, t) = c.fresh_local(list_t.clone());
                let ih_ty = eq_list(map_app(&fi, &map_app(&f, &t)), t.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let fh = Expr::app(fi.clone(), Expr::app(f.clone(), h.clone())); // finv (f h)
                let m = map_app(&fi, &map_app(&f, &t)); // listMap finv (listMap f t)
                                                        // tail_congr : cons (finv (f h)) m = cons (finv (f h)) t   (congrArg via ih)
                let tail_f = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, x) = d.fresh_local(list_t.clone());
                    d.finish_child(d.mk_lam(
                        x_id,
                        BinderInfo::Default,
                        list_t.clone(),
                        cons_e(&fh, &x),
                    ))
                };
                let tail_congr = Expr::apps(
                    congr.clone(),
                    [
                        list_t.clone(),
                        list_t.clone(),
                        m.clone(),
                        t.clone(),
                        tail_f,
                        ih.clone(),
                    ],
                );
                // head_congr : cons (finv (f h)) t = cons h t   (congrArg via hinv h)
                let head_f = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, x) = d.fresh_local(nat.clone());
                    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, nat.clone(), cons_e(&x, &t)))
                };
                let hinv_h = Expr::app(hinv.clone(), h.clone()); // finv (f h) = h
                let head_congr = Expr::apps(
                    congr.clone(),
                    [
                        nat.clone(),
                        list_t.clone(),
                        fh.clone(),
                        h.clone(),
                        head_f,
                        hinv_h,
                    ],
                );
                // Eq.trans : cons (finv (f h)) m = cons h t
                let trans = Expr::apps(
                    eq_trans.clone(),
                    [
                        list_t.clone(),
                        cons_e(&fh, &m),
                        cons_e(&fh, &t),
                        cons_e(&h, &t),
                        tail_congr,
                        head_congr,
                    ],
                );
                let e = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, trans);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let rec = Expr::apps(
                list_rec(Level::zero()),
                [nat.clone(), motive, nil_proof, cons_proof, l.clone()],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), rec);
            let e = b.mk_lam(hinv_id, BinderInfo::Default, hinv_ty, e);
            let e = b.mk_lam(fi_id, BinderInfo::Default, nat_to_nat.clone(), e);
            b.finish(b.mk_lam(f_id, BinderInfo::Default, nat_to_nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LOOP_MAP_ROUNDTRIP),
            level_params: vec![],
            type_: mrt_type,
            value: mrt_val,
        })?;

        // ── TYPE-POLYMORPHIC loop give-back: any reversible element op over ANY element
        //    type A (Type u), not just Nat. The fully general loop backward function.
        let ulp = Name::from_string("u");
        let ulp_lvl = Level::param(ulp.clone());
        let ulps = Level::succ(ulp_lvl.clone());
        let type_u = Expr::sort(ulps.clone());
        let list_ct = Expr::const_(Name::from_string("List"), vec![ulp_lvl.clone()]);
        let list_u = |a: &Expr| Expr::app(list_ct.clone(), a.clone());
        let nil_ct = Expr::const_(Name::from_string("List.nil"), vec![ulp_lvl.clone()]);
        let cons_ct = Expr::const_(Name::from_string("List.cons"), vec![ulp_lvl.clone()]);
        let cons_u = |a: &Expr, h: &Expr, t: &Expr| {
            Expr::apps(cons_ct.clone(), [a.clone(), h.clone(), t.clone()])
        };
        let eqc_tu = Expr::const_(Name::from_string("Eq"), vec![ulps.clone()]);
        let refl_tu = Expr::const_(Name::from_string("Eq.refl"), vec![ulps.clone()]);
        let congr_tu = Expr::const_(
            Name::from_string("congrArg"),
            vec![ulps.clone(), ulps.clone()],
        );
        let trans_tu = Expr::const_(Name::from_string("Eq.trans"), vec![ulps.clone()]);
        let listrec_u =
            |mlvl: Level| Expr::const_(Name::from_string("List.rec"), vec![mlvl, ulp_lvl.clone()]);
        let a_to_a = |a: &Expr| Expr::arrow(a.clone(), a.clone());

        // listMapT.{u} : {A : Type u} → (A → A) → List A → List A
        //   := λ {A} g l => List.rec.{u+1,u} A (λ_=>List A) nil (λ h t rec => cons (g h) rec) l
        let mapt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let t = Expr::arrow(a_to_a(&a), Expr::arrow(list_u(&a), list_u(&a)));
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), t))
        };
        let mapt_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (g_id, g) = b.fresh_local(a_to_a(&a));
            let (l_id, l) = b.fresh_local(list_u(&a));
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ll_id, _ll) = c.fresh_local(list_u(&a));
                c.finish_child(c.mk_lam(ll_id, BinderInfo::Default, list_u(&a), list_u(&a)))
            };
            let cons_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(a.clone());
                let (t_id, _t) = c.fresh_local(list_u(&a));
                let (r_id, r) = c.fresh_local(list_u(&a));
                let body = cons_u(&a, &Expr::app(g.clone(), h.clone()), &r);
                let e = c.mk_lam(r_id, BinderInfo::Default, list_u(&a), body);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_u(&a), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, a.clone(), e))
            };
            let rec = Expr::apps(
                listrec_u(ulps.clone()),
                [
                    a.clone(),
                    motive,
                    Expr::app(nil_ct.clone(), a.clone()),
                    cons_minor,
                    l.clone(),
                ],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_u(&a), rec);
            let e = b.mk_lam(g_id, BinderInfo::Default, a_to_a(&a), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_LOOP_MAP_T),
            level_params: vec![ulp.clone()],
            type_: mapt_type,
            value: mapt_val,
            is_reducible: true,
        })?;
        let mapt_ct = Expr::const_(
            Name::from_string(GIVEBACK_LOOP_MAP_T),
            vec![ulp_lvl.clone()],
        );
        let mapt_app = |a: &Expr, g: &Expr, l: &Expr| {
            Expr::apps(mapt_ct.clone(), [a.clone(), g.clone(), l.clone()])
        };
        let eq_lu = |a: &Expr, x: Expr, y: Expr| Expr::apps(eqc_tu.clone(), [list_u(a), x, y]);
        let eq_au = |a: &Expr, x: Expr, y: Expr| Expr::apps(eqc_tu.clone(), [a.clone(), x, y]);
        let refl_lu = |a: &Expr, x: Expr| Expr::apps(refl_tu.clone(), [list_u(a), x]);

        // listMapT_roundTrip.{u} : {A} → ∀ f finv, (∀ x, finv (f x) = x) →
        //                            ∀ l, listMapT finv (listMapT f l) = l
        let mtrt_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (f_id, f) = b.fresh_local(a_to_a(&a));
            let (fi_id, fi) = b.fresh_local(a_to_a(&a));
            let hinv_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(a.clone());
                let concl = eq_au(
                    &a,
                    Expr::app(fi.clone(), Expr::app(f.clone(), x.clone())),
                    x.clone(),
                );
                c.finish_child(c.mk_pi(x_id, BinderInfo::Default, a.clone(), concl))
            };
            let (hinv_id, _hinv) = b.fresh_local(hinv_ty.clone());
            let (l_id, l) = b.fresh_local(list_u(&a));
            let concl = eq_lu(&a, mapt_app(&a, &fi, &mapt_app(&a, &f, &l)), l.clone());
            let e = b.mk_pi(l_id, BinderInfo::Default, list_u(&a), concl);
            let e = b.mk_pi(hinv_id, BinderInfo::Default, hinv_ty, e);
            let e = b.mk_pi(fi_id, BinderInfo::Default, a_to_a(&a), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, a_to_a(&a), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        let mtrt_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(type_u.clone());
            let (f_id, f) = b.fresh_local(a_to_a(&a));
            let (fi_id, fi) = b.fresh_local(a_to_a(&a));
            let hinv_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(a.clone());
                let concl = eq_au(
                    &a,
                    Expr::app(fi.clone(), Expr::app(f.clone(), x.clone())),
                    x.clone(),
                );
                c.finish_child(c.mk_pi(x_id, BinderInfo::Default, a.clone(), concl))
            };
            let (hinv_id, hinv) = b.fresh_local(hinv_ty.clone());
            let (l_id, l) = b.fresh_local(list_u(&a));
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ll_id, ll) = c.fresh_local(list_u(&a));
                let body = eq_lu(&a, mapt_app(&a, &fi, &mapt_app(&a, &f, &ll)), ll.clone());
                c.finish_child(c.mk_lam(ll_id, BinderInfo::Default, list_u(&a), body))
            };
            let nil_proof = refl_lu(&a, Expr::app(nil_ct.clone(), a.clone()));
            let cons_proof = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(a.clone());
                let (t_id, t) = c.fresh_local(list_u(&a));
                let ih_ty = eq_lu(&a, mapt_app(&a, &fi, &mapt_app(&a, &f, &t)), t.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let fh = Expr::app(fi.clone(), Expr::app(f.clone(), h.clone()));
                let m = mapt_app(&a, &fi, &mapt_app(&a, &f, &t));
                let tail_f = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, x) = d.fresh_local(list_u(&a));
                    d.finish_child(d.mk_lam(
                        x_id,
                        BinderInfo::Default,
                        list_u(&a),
                        cons_u(&a, &fh, &x),
                    ))
                };
                let tail_congr = Expr::apps(
                    congr_tu.clone(),
                    [
                        list_u(&a),
                        list_u(&a),
                        m.clone(),
                        t.clone(),
                        tail_f,
                        ih.clone(),
                    ],
                );
                let head_f = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, x) = d.fresh_local(a.clone());
                    d.finish_child(d.mk_lam(
                        x_id,
                        BinderInfo::Default,
                        a.clone(),
                        cons_u(&a, &x, &t),
                    ))
                };
                let hinv_h = Expr::app(hinv.clone(), h.clone());
                let head_congr = Expr::apps(
                    congr_tu.clone(),
                    [a.clone(), list_u(&a), fh.clone(), h.clone(), head_f, hinv_h],
                );
                let trans = Expr::apps(
                    trans_tu.clone(),
                    [
                        list_u(&a),
                        cons_u(&a, &fh, &m),
                        cons_u(&a, &fh, &t),
                        cons_u(&a, &h, &t),
                        tail_congr,
                        head_congr,
                    ],
                );
                let e = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, trans);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_u(&a), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, a.clone(), e))
            };
            let rec = Expr::apps(
                listrec_u(Level::zero()),
                [a.clone(), motive, nil_proof, cons_proof, l.clone()],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_u(&a), rec);
            let e = b.mk_lam(hinv_id, BinderInfo::Default, hinv_ty, e);
            let e = b.mk_lam(fi_id, BinderInfo::Default, a_to_a(&a), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, a_to_a(&a), e);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, type_u.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LOOP_MAP_T_ROUNDTRIP),
            level_params: vec![ulp.clone()],
            type_: mtrt_type,
            value: mtrt_val,
        })?;

        // ── Concrete demonstration the general loop law is NOT +k-locked: a boolean-flip
        //    loop `for b in &mut l { *b = !*b }` gives back via listMapT at A=Bool, op=not
        //    (self-inverse) — zero new induction, just not_not + the general law applied.
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_not = Expr::const_(Name::from_string("Bool.not"), vec![]);
        let not_a = |x: &Expr| Expr::app(bool_not.clone(), x.clone());
        let eqc_b = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl_b = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let eq_bool = |x: Expr, y: Expr| Expr::apps(eqc_b.clone(), [bool_c.clone(), x, y]);
        let refl_bool = |x: Expr| Expr::apps(eq_refl_b.clone(), [bool_c.clone(), x]);

        // not_not : ∀ b, Bool.not (Bool.not b) = b   (Bool.rec.{0}, ι per case)
        let nn_type = {
            let mut b = EnvDeclBuilder::new();
            let (bb_id, bb) = b.fresh_local(bool_c.clone());
            let concl = eq_bool(not_a(&not_a(&bb)), bb.clone());
            b.finish(b.mk_pi(bb_id, BinderInfo::Default, bool_c.clone(), concl))
        };
        let nn_val = {
            let mut b = EnvDeclBuilder::new();
            let (bb_id, bb) = b.fresh_local(bool_c.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(bool_c.clone());
                let body = eq_bool(not_a(&not_a(&x)), x.clone());
                c.finish_child(c.mk_lam(x_id, BinderInfo::Default, bool_c.clone(), body))
            };
            let body = Expr::apps(
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
                [
                    motive,
                    refl_bool(bfalse.clone()),
                    refl_bool(btrue.clone()),
                    bb.clone(),
                ],
            );
            b.finish(b.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LOOP_NOT_NOT),
            level_params: vec![],
            type_: nn_type,
            value: nn_val,
        })?;

        // boolNotLoop_roundTrip : ∀ l : List Bool, listMapT not (listMapT not l) = l
        //   := listMapT_roundTrip.{0} Bool Bool.not Bool.not not_not   (instance, no induction)
        let list_bool = Expr::app(
            Expr::const_(Name::from_string("List"), vec![u0.clone()]),
            bool_c.clone(),
        );
        let mapt_b = |l: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string(GIVEBACK_LOOP_MAP_T), vec![u0.clone()]),
                [bool_c.clone(), bool_not.clone(), l.clone()],
            )
        };
        let bnl_type = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_bool.clone());
            let concl = Expr::apps(
                eqc_b.clone(),
                [list_bool.clone(), mapt_b(&mapt_b(&l)), l.clone()],
            );
            b.finish(b.mk_pi(l_id, BinderInfo::Default, list_bool.clone(), concl))
        };
        let bnl_val = Expr::apps(
            Expr::const_(
                Name::from_string(GIVEBACK_LOOP_MAP_T_ROUNDTRIP),
                vec![u0.clone()],
            ),
            [
                bool_c.clone(),
                bool_not.clone(),
                bool_not.clone(),
                Expr::const_(Name::from_string(GIVEBACK_LOOP_NOT_NOT), vec![]),
            ],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LOOP_BOOLNOT_ROUNDTRIP),
            level_params: vec![],
            type_: bnl_type,
            value: bnl_val,
        })?;

        // ── THIRD recognized invertible op, over a STRUCTURED element type: a loop over a
        //    sequence of pairs incrementing field 0 (`for p in &mut l { p.0 += 1 }`). The
        //    element inverse is `Eq.refl` (Nat.sub ι + Prod structure-eta); instantiates
        //    listMapT_roundTrip at A = Prod Nat Nat. Loop over `Vec<Struct>` mutating a field.
        let plv = vec![u0.clone(), u0.clone()];
        let prod_ct = Expr::const_(Name::from_string("Prod"), plv.clone());
        let pnn = Expr::apps(prod_ct.clone(), [nat.clone(), nat.clone()]);
        let prod_mk = Expr::const_(Name::from_string("Prod.mk"), plv.clone());
        let prod_fst = Expr::const_(Name::from_string("Prod.fst"), plv.clone());
        let prod_snd = Expr::const_(Name::from_string("Prod.snd"), plv);
        let mkp = |a: &Expr, b: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [nat.clone(), nat.clone(), a.clone(), b.clone()],
            )
        };
        let fstp = |p: &Expr| Expr::apps(prod_fst.clone(), [nat.clone(), nat.clone(), p.clone()]);
        let sndp = |p: &Expr| Expr::apps(prod_snd.clone(), [nat.clone(), nat.clone(), p.clone()]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let one_lit = Expr::nat_lit(1);
        // inc = λ p => Prod.mk (p.fst + 1) p.snd
        let inc_fn = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pnn.clone());
            let body = mkp(
                &Expr::apps(nat_add.clone(), [fstp(&p), one_lit.clone()]),
                &sndp(&p),
            );
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pnn.clone(), body))
        };
        // dec = λ p => Prod.mk (Nat.sub p.fst 1) p.snd
        let dec_fn = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pnn.clone());
            let body = mkp(
                &Expr::apps(nat_sub.clone(), [fstp(&p), one_lit.clone()]),
                &sndp(&p),
            );
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pnn.clone(), body))
        };
        // pairIncrInverse : ∀ p, dec (inc p) = p   (Eq.refl via Nat.sub ι + structure-eta)
        let eqc_p = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl_p = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let inverse_fn = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(pnn.clone());
            let body = Expr::apps(eq_refl_p.clone(), [pnn.clone(), p.clone()]);
            b.finish(b.mk_lam(p_id, BinderInfo::Default, pnn.clone(), body))
        };
        // pairIncrLoop_roundTrip := listMapT_roundTrip.{0} (Prod Nat Nat) inc dec inverse
        let mapt_p = |g: &Expr, l: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string(GIVEBACK_LOOP_MAP_T), vec![u0.clone()]),
                [pnn.clone(), g.clone(), l.clone()],
            )
        };
        let list_pnn = Expr::app(
            Expr::const_(Name::from_string("List"), vec![u0.clone()]),
            pnn.clone(),
        );
        let pil_type = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_pnn.clone());
            let concl = Expr::apps(
                eqc_p.clone(),
                [
                    list_pnn.clone(),
                    mapt_p(&dec_fn, &mapt_p(&inc_fn, &l)),
                    l.clone(),
                ],
            );
            b.finish(b.mk_pi(l_id, BinderInfo::Default, list_pnn.clone(), concl))
        };
        let pil_val = Expr::apps(
            Expr::const_(
                Name::from_string(GIVEBACK_LOOP_MAP_T_ROUNDTRIP),
                vec![u0.clone()],
            ),
            [
                pnn.clone(),
                inc_fn.clone(),
                dec_fn.clone(),
                inverse_fn.clone(),
            ],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_LOOP_PAIRINCR_ROUNDTRIP),
            level_params: vec![],
            type_: pil_type,
            value: pil_val,
        })?;

        Ok(())
    }

    /// Build the **generic give-back** anchor — `fn f<T>(x: &mut T)`. The
    /// value-polymorphic give-back memory law `read_after_write_poly : ∀ (α:Type)…`
    /// (admitted by [`Environment::init_giveback_refinement`]) is the generic
    /// statement; this anchor INSTANTIATES it at concrete `T` to show the generic
    /// give-back specializes by APPLICATION (no reproof) to a scalar (`Nat`), a
    /// different scalar (`Bool`), and a STRUCT (`Prod Nat Nat`). Each instance's
    /// proof TERM is just `read_after_write_poly T`, so its axiom closure equals the
    /// (axiom-clean) generic law's. This is monomorphization made sound: one proof
    /// covers every `T`.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite or an instantiation fails to admit.
    pub fn init_giveback_generics_refinement(&mut self) -> Result<(), EnvError> {
        // init_giveback_refinement is not idempotent (re-admits backId); guard so
        // this anchor is safe whether or not the base anchor was already built.
        if self
            .get_const(&Name::from_string(GIVEBACK_BACK_ID))
            .is_none()
        {
            self.init_giveback_refinement()?; // gbLookupP/gbUpdateP/read_after_write_poly
        }
        self.init_bool()?;
        self.init_prod()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let one = Level::succ(Level::zero());
        let zero = Level::zero();
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![one]);
        let gb_lookup_p = Expr::const_(Name::from_string("RustSem.GiveBack.gbLookupP"), vec![]);
        let gb_update_p = Expr::const_(Name::from_string("RustSem.GiveBack.gbUpdateP"), vec![]);
        let poly = Expr::const_(Name::from_string(GIVEBACK_READ_AFTER_WRITE_POLY), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let prod_nat_nat = Expr::apps(
            Expr::const_(Name::from_string("Prod"), vec![zero.clone(), zero.clone()]),
            [nat.clone(), nat.clone()],
        );

        // Admit `genericRaw_T : ∀ (s:Nat→T)(k:Nat)(v:T), gbLookupP T (gbUpdateP T s k v) k = v`
        //   := read_after_write_poly T    (the poly law specialized; T : Type 0 = Sort 1).
        let mut admit_inst =
            |env: &mut Environment, name: &str, t: &Expr| -> Result<(), EnvError> {
                let store_t = Expr::arrow(nat.clone(), t.clone());
                let ty = {
                    let mut b = EnvDeclBuilder::new();
                    let (s_id, s) = b.fresh_local(store_t.clone());
                    let (k_id, k) = b.fresh_local(nat.clone());
                    let (v_id, v) = b.fresh_local(t.clone());
                    let lhs = Expr::apps(
                        gb_lookup_p.clone(),
                        [
                            t.clone(),
                            Expr::apps(
                                gb_update_p.clone(),
                                [t.clone(), s.clone(), k.clone(), v.clone()],
                            ),
                            k.clone(),
                        ],
                    );
                    let concl = Expr::apps(eq1.clone(), [t.clone(), lhs, v.clone()]);
                    let e = b.mk_pi(v_id, BinderInfo::Default, t.clone(), concl);
                    let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
                    let e = b.mk_pi(s_id, BinderInfo::Default, store_t.clone(), e);
                    b.finish(e)
                };
                let val = Expr::app(poly.clone(), t.clone());
                env.add_decl(Declaration::Theorem {
                    name: Name::from_string(name),
                    level_params: vec![],
                    type_: ty,
                    value: val,
                })
            };
        admit_inst(self, GIVEBACK_GEN_NAT, &nat.clone())?;
        admit_inst(self, GIVEBACK_GEN_BOOL, &bool_c)?;
        admit_inst(self, GIVEBACK_GEN_PROD, &prod_nat_nat)?;

        Ok(())
    }

    /// Build the **closure give-back** anchor — an `FnMut` reconstructs its
    /// captured environment. A closure `move |y| { *cap += y }` capturing a `&mut`
    /// (`cap`) and a by-ref value carries an env modelled as `(mutCap, refCap) :
    /// Prod Nat Nat`. One call mutates the `mut` capture and FRAMES the `ref`
    /// capture:
    ///
    ///   closureCall e y := Prod.mk (e.fst + y) e.snd
    ///
    /// Proves (axiom-clean): call-effect (`(closureCall e y).fst = e.fst + y`, ι),
    /// frame (`(closureCall e y).snd = e.snd`, ι), and the **no-op call**
    /// `∀ e, closureCall e 0 = e` (the env give-back reconstructs the WHOLE captured
    /// environment unchanged — `Nat.add e.fst 0 = e.fst` by ι then structure-eta on
    /// the env). The no-op-call law is the closure-give-back property a skeptic
    /// checks: an `FnMut` whose body is a no-op gives back exactly its env.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Prod`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_closure_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_prod()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Level::zero();
        let lv = vec![zero.clone(), zero.clone()];
        let one = Level::succ(Level::zero());
        let env_t = Expr::apps(
            Expr::const_(Name::from_string("Prod"), lv.clone()),
            [nat.clone(), nat.clone()],
        );
        let prod_mk = Expr::const_(Name::from_string("Prod.mk"), lv.clone());
        let prod_fst = Expr::const_(Name::from_string("Prod.fst"), lv.clone());
        let prod_snd = Expr::const_(Name::from_string("Prod.snd"), lv);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let zero_lit = Expr::nat_lit(0);

        let mk = |a: &Expr, b: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [nat.clone(), nat.clone(), a.clone(), b.clone()],
            )
        };
        let fst = |e: &Expr| Expr::apps(prod_fst.clone(), [nat.clone(), nat.clone(), e.clone()]);
        let snd = |e: &Expr| Expr::apps(prod_snd.clone(), [nat.clone(), nat.clone(), e.clone()]);
        let add = |a: Expr, b: Expr| Expr::apps(nat_add.clone(), [a, b]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);
        let eq_env = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [env_t.clone(), l, r]);
        let refl_nat = |x: Expr| Expr::apps(eq_refl.clone(), [nat.clone(), x]);
        let refl_env = |x: Expr| Expr::apps(eq_refl.clone(), [env_t.clone(), x]);

        // closureCall : Prod Nat Nat → Nat → Prod Nat Nat
        //   := λ e y => Prod.mk (Nat.add (e.fst) y) (e.snd)
        let call_val = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(env_t.clone());
            let (y_id, y) = b.fresh_local(nat.clone());
            let body = mk(&add(fst(&e), y.clone()), &snd(&e));
            let lam = b.mk_lam(y_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(e_id, BinderInfo::Default, env_t.clone(), lam))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_CLO_CALL),
            level_params: vec![],
            type_: Expr::arrow(env_t.clone(), Expr::arrow(nat.clone(), env_t.clone())),
            value: call_val,
            is_reducible: true,
        })?;
        let clo = Expr::const_(Name::from_string(GIVEBACK_CLO_CALL), vec![]);
        let call = |e: &Expr, y: &Expr| Expr::apps(clo.clone(), [e.clone(), y.clone()]);

        // call-effect : ∀ e y, (closureCall e y).fst = e.fst + y   (ι)
        let eff_type = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(env_t.clone());
            let (y_id, y) = b.fresh_local(nat.clone());
            let concl = eq_nat(fst(&call(&e, &y)), add(fst(&e), y.clone()));
            let e2 = b.mk_pi(y_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, env_t.clone(), e2))
        };
        let eff_val = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(env_t.clone());
            let (y_id, y) = b.fresh_local(nat.clone());
            let body = refl_nat(add(fst(&e), y.clone()));
            let lam = b.mk_lam(y_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(e_id, BinderInfo::Default, env_t.clone(), lam))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_CLO_CALL_EFFECT),
            level_params: vec![],
            type_: eff_type,
            value: eff_val,
        })?;

        // frame : ∀ e y, (closureCall e y).snd = e.snd   (ι; by-ref capture untouched)
        let fr_type = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(env_t.clone());
            let (y_id, y) = b.fresh_local(nat.clone());
            let concl = eq_nat(snd(&call(&e, &y)), snd(&e));
            let e2 = b.mk_pi(y_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(e_id, BinderInfo::Default, env_t.clone(), e2))
        };
        let fr_val = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(env_t.clone());
            let (y_id, _y) = b.fresh_local(nat.clone());
            let body = refl_nat(snd(&e));
            let lam = b.mk_lam(y_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(e_id, BinderInfo::Default, env_t.clone(), lam))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_CLO_FRAME),
            level_params: vec![],
            type_: fr_type,
            value: fr_val,
        })?;

        // no-op : ∀ e, closureCall e 0 = e   (Nat.add e.fst 0 = e.fst by ι, then env eta)
        let noop_type = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(env_t.clone());
            let concl = eq_env(call(&e, &zero_lit), e.clone());
            b.finish(b.mk_pi(e_id, BinderInfo::Default, env_t.clone(), concl))
        };
        let noop_val = {
            let mut b = EnvDeclBuilder::new();
            let (e_id, e) = b.fresh_local(env_t.clone());
            b.finish(b.mk_lam(e_id, BinderInfo::Default, env_t.clone(), refl_env(e)))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_CLO_NOOP),
            level_params: vec![],
            type_: noop_type,
            value: noop_val,
        })?;

        Ok(())
    }

    /// Build the **trait give-back** anchor — dynamic dispatch through a vtable
    /// (trait objects). A `dyn Trait` is modelled as a vtable `(method, data) :
    /// Prod (Nat→Nat) Nat`; a method call PROJECTS the method out of the vtable and
    /// applies it:
    ///
    ///   vtblDispatch v x := (v.fst) x
    ///
    /// Proves (axiom-clean): the dyn-dispatch fact `∀ f d x, vtblDispatch (mk f d)
    /// x = f x` (the call resolves to whatever method the vtable carries — the call
    /// site is impl-agnostic; proj-ι), plus two concrete impls resolving to
    /// different give-back methods — identity (`dispatch (mk (λz.z) d) x = x`) and
    /// increment (`dispatch (mk (λz.z+1) d) x = x+1`) — by proj-ι + β. This is the
    /// trait-object give-back: the method's backward function is selected at runtime
    /// from the vtable.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Prod`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_trait_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_prod()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Level::zero();
        let lv = vec![zero.clone(), zero.clone()];
        let one = Level::succ(Level::zero());
        let fn_ty = Expr::arrow(nat.clone(), nat.clone()); // Nat → Nat : Type 0 = Sort 1
        let vtbl_t = Expr::apps(
            Expr::const_(Name::from_string("Prod"), lv.clone()),
            [fn_ty.clone(), nat.clone()],
        );
        let prod_mk = Expr::const_(Name::from_string("Prod.mk"), lv.clone());
        let prod_fst = Expr::const_(Name::from_string("Prod.fst"), lv);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let one_lit = Expr::nat_lit(1);

        let mk_v = |f: &Expr, d: &Expr| {
            Expr::apps(
                prod_mk.clone(),
                [fn_ty.clone(), nat.clone(), f.clone(), d.clone()],
            )
        };
        let fst_v =
            |v: &Expr| Expr::apps(prod_fst.clone(), [fn_ty.clone(), nat.clone(), v.clone()]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);
        let refl_nat = |x: Expr| Expr::apps(eq_refl.clone(), [nat.clone(), x]);
        let add = |a: Expr, b: Expr| Expr::apps(nat_add.clone(), [a, b]);
        // Closed method terms (the "impls").
        let id_fn = || {
            let mut b = EnvDeclBuilder::new();
            let (z_id, z) = b.fresh_local(nat.clone());
            b.finish(b.mk_lam(z_id, BinderInfo::Default, nat.clone(), z))
        };
        let incr_fn = || {
            let mut b = EnvDeclBuilder::new();
            let (z_id, z) = b.fresh_local(nat.clone());
            let body = add(z.clone(), one_lit.clone());
            b.finish(b.mk_lam(z_id, BinderInfo::Default, nat.clone(), body))
        };

        // vtblDispatch : Prod (Nat→Nat) Nat → Nat → Nat := λ v x => (v.fst) x
        let dispatch_val = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(vtbl_t.clone());
            let (x_id, x) = b.fresh_local(nat.clone());
            let body = Expr::app(fst_v(&v), x);
            let lam = b.mk_lam(x_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(v_id, BinderInfo::Default, vtbl_t.clone(), lam))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_TRAIT_DISPATCH),
            level_params: vec![],
            type_: Expr::arrow(vtbl_t.clone(), Expr::arrow(nat.clone(), nat.clone())),
            value: dispatch_val,
            is_reducible: true,
        })?;
        let dispatch = Expr::const_(Name::from_string(GIVEBACK_TRAIT_DISPATCH), vec![]);
        let disp = |v: &Expr, x: &Expr| Expr::apps(dispatch.clone(), [v.clone(), x.clone()]);

        // resolves : ∀ (f:Nat→Nat) d x, vtblDispatch (mk f d) x = f x   (proj-ι)
        let res_type = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(fn_ty.clone());
            let (d_id, d) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(nat.clone());
            let concl = eq_nat(disp(&mk_v(&f, &d), &x), Expr::app(f.clone(), x.clone()));
            let e = b.mk_pi(x_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(d_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(f_id, BinderInfo::Default, fn_ty.clone(), e))
        };
        let res_val = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(fn_ty.clone());
            let (d_id, _d) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(nat.clone());
            let body = refl_nat(Expr::app(f.clone(), x.clone()));
            let e = b.mk_lam(x_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(d_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(f_id, BinderInfo::Default, fn_ty.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_TRAIT_RESOLVES),
            level_params: vec![],
            type_: res_type,
            value: res_val,
        })?;

        // id-impl : ∀ d x, vtblDispatch (mk (λz.z) d) x = x   (proj-ι + β)
        let id_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(nat.clone());
            let concl = eq_nat(disp(&mk_v(&id_fn(), &d), &x), x.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(d_id, BinderInfo::Default, nat.clone(), e))
        };
        let id_val = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, _d) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(nat.clone());
            let e = b.mk_lam(x_id, BinderInfo::Default, nat.clone(), refl_nat(x));
            b.finish(b.mk_lam(d_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_TRAIT_ID),
            level_params: vec![],
            type_: id_type,
            value: id_val,
        })?;

        // incr-impl : ∀ d x, vtblDispatch (mk (λz.z+1) d) x = x + 1   (proj-ι + β)
        let incr_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(nat.clone());
            let concl = eq_nat(
                disp(&mk_v(&incr_fn(), &d), &x),
                add(x.clone(), one_lit.clone()),
            );
            let e = b.mk_pi(x_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(d_id, BinderInfo::Default, nat.clone(), e))
        };
        let incr_val = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, _d) = b.fresh_local(nat.clone());
            let (x_id, x) = b.fresh_local(nat.clone());
            let body = refl_nat(add(x.clone(), one_lit.clone()));
            let e = b.mk_lam(x_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(d_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_TRAIT_INCR),
            level_params: vec![],
            type_: incr_type,
            value: incr_val,
        })?;

        // ── ASSOCIATED-TYPE give-back: a trait `Container { type Item; fn bump(&mut
        //    Self::Item) }` with an impl resolving `Item = Nat`. The give-back of
        //    `&mut Self::Item` incrementing resolves DEFINITIONALLY (via the impl) to the
        //    give-back at the concrete type Nat — an associated type is a type-level
        //    indirection that does not obstruct give-back.
        // assocItem : Type := Nat   (<NatContainer as Container>::Item)
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_ASSOC_ITEM),
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: nat.clone(),
            is_reducible: true,
        })?;
        let assoc_item = Expr::const_(Name::from_string(GIVEBACK_ASSOC_ITEM), vec![]);
        // assocIncrBack : assocItem → assocItem := λ v => Nat.add v 1
        let aib_val = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(assoc_item.clone());
            let body = add(v.clone(), one_lit.clone());
            b.finish(b.mk_lam(v_id, BinderInfo::Default, assoc_item.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_ASSOC_INCR_BACK),
            level_params: vec![],
            type_: Expr::arrow(assoc_item.clone(), assoc_item.clone()),
            value: aib_val,
            is_reducible: true,
        })?;
        let assoc_incr_back = Expr::const_(Name::from_string(GIVEBACK_ASSOC_INCR_BACK), vec![]);
        // assoc_incr_roundTrip : ∀ (v : assocItem), assocIncrBack v = Nat.add v 1
        //   := λ v => Eq.refl  (assocIncrBack v ≡ v+1 by δ; assocItem ≡ Nat by resolution)
        let air_type = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(assoc_item.clone());
            let concl = eq_nat(
                Expr::app(assoc_incr_back.clone(), v.clone()),
                add(v.clone(), one_lit.clone()),
            );
            b.finish(b.mk_pi(v_id, BinderInfo::Default, assoc_item.clone(), concl))
        };
        let air_val = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(assoc_item.clone());
            let body = refl_nat(add(v.clone(), one_lit.clone()));
            b.finish(b.mk_lam(v_id, BinderInfo::Default, assoc_item.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_ASSOC_INCR),
            level_params: vec![],
            type_: air_type,
            value: air_val,
        })?;

        Ok(())
    }

    /// Build the **Vec/std-collection give-back** anchor — a `Vec<Nat>` used as a
    /// stack (modelled by `List Nat`). `Vec::push` prepends; reading the front
    /// (`vecHead`) and the rest (`vecTail`) are `List.rec` folds. Proves the
    /// push/pop round-trip (axiom-clean, ι):
    ///
    ///   vec_pushPopHead `∀ x v, vecHead (vecPush x v) = x`   (pop returns what was pushed)
    ///   vec_pushPopTail `∀ x v, vecTail (vecPush x v) = v`   (the rest is unchanged)
    ///
    /// This is the std-collection give-back: a `Vec` operation and its inverse
    /// round-trip, the LIFO discipline a skeptic checks for container types.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `List`) or a give-back
    /// declaration fails to admit / type-check.
    pub fn init_giveback_vec_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?;
        self.init_list()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let u0 = Level::zero();
        let one = Level::succ(Level::zero());
        let list_t = Expr::app(
            Expr::const_(Name::from_string("List"), vec![u0.clone()]),
            nat.clone(),
        );
        let list_nil_c = Expr::const_(Name::from_string("List.nil"), vec![u0.clone()]);
        let list_cons_c = Expr::const_(Name::from_string("List.cons"), vec![u0.clone()]);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]);
        let zero_lit = Expr::nat_lit(0);

        let nil_e = Expr::app(list_nil_c.clone(), nat.clone());
        let cons_e = |h: &Expr, t: &Expr| {
            Expr::apps(list_cons_c.clone(), [nat.clone(), h.clone(), t.clone()])
        };
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);
        let eq_list = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [list_t.clone(), l, r]);
        let refl_nat = |x: Expr| Expr::apps(eq_refl.clone(), [nat.clone(), x]);
        let refl_list = |x: Expr| Expr::apps(eq_refl.clone(), [list_t.clone(), x]);
        let list_rec = |motive_lvl: Level| {
            Expr::const_(Name::from_string("List.rec"), vec![motive_lvl, u0.clone()])
        };

        // vecPush : Nat → List Nat → List Nat := λ x v => cons x v
        let push_val = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(list_t.clone());
            let body = cons_e(&x, &v);
            let e = b.mk_lam(v_id, BinderInfo::Default, list_t.clone(), body);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_VEC_PUSH),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), Expr::arrow(list_t.clone(), list_t.clone())),
            value: push_val,
            is_reducible: true,
        })?;
        let vec_push = Expr::const_(Name::from_string(GIVEBACK_VEC_PUSH), vec![]);
        let push = |x: &Expr, v: &Expr| Expr::apps(vec_push.clone(), [x.clone(), v.clone()]);

        // vecHead : List Nat → Nat := List.rec.{1,0} Nat (λ_=>Nat) 0 (λ h t _ => h)
        let head_val = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(list_t.clone());
                c.finish_child(c.mk_lam(m_id, BinderInfo::Default, list_t.clone(), nat.clone()))
            };
            let cons_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(nat.clone());
                let (t_id, _t) = c.fresh_local(list_t.clone());
                let (r_id, _r) = c.fresh_local(nat.clone());
                let e = c.mk_lam(r_id, BinderInfo::Default, nat.clone(), h);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let body = Expr::apps(
                list_rec(one.clone()),
                [nat.clone(), motive, zero_lit.clone(), cons_minor, l.clone()],
            );
            b.finish(b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_VEC_HEAD),
            level_params: vec![],
            type_: Expr::arrow(list_t.clone(), nat.clone()),
            value: head_val,
            is_reducible: true,
        })?;
        let vec_head = Expr::const_(Name::from_string(GIVEBACK_VEC_HEAD), vec![]);

        // vecTail : List Nat → List Nat := List.rec.{1,0} Nat (λ_=>List Nat) nil (λ h t _ => t)
        let tail_val = {
            let mut b = EnvDeclBuilder::new();
            let (l_id, l) = b.fresh_local(list_t.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(list_t.clone());
                c.finish_child(c.mk_lam(m_id, BinderInfo::Default, list_t.clone(), list_t.clone()))
            };
            let cons_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, _h) = c.fresh_local(nat.clone());
                let (t_id, t) = c.fresh_local(list_t.clone());
                let (r_id, _r) = c.fresh_local(list_t.clone());
                let e = c.mk_lam(r_id, BinderInfo::Default, list_t.clone(), t);
                let e = c.mk_lam(t_id, BinderInfo::Default, list_t.clone(), e);
                c.finish_child(c.mk_lam(h_id, BinderInfo::Default, nat.clone(), e))
            };
            let body = Expr::apps(
                list_rec(one.clone()),
                [nat.clone(), motive, nil_e.clone(), cons_minor, l.clone()],
            );
            b.finish(b.mk_lam(l_id, BinderInfo::Default, list_t.clone(), body))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_VEC_TAIL),
            level_params: vec![],
            type_: Expr::arrow(list_t.clone(), list_t.clone()),
            value: tail_val,
            is_reducible: true,
        })?;
        let vec_tail = Expr::const_(Name::from_string(GIVEBACK_VEC_TAIL), vec![]);

        // push-pop-head : ∀ x v, vecHead (vecPush x v) = x   (ι)
        let pph_type = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(list_t.clone());
            let concl = eq_nat(Expr::app(vec_head.clone(), push(&x, &v)), x.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, list_t.clone(), concl);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, nat.clone(), e))
        };
        let pph_val = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nat.clone());
            let (v_id, _v) = b.fresh_local(list_t.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, list_t.clone(), refl_nat(x));
            b.finish(b.mk_lam(x_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_VEC_PUSH_POP_HEAD),
            level_params: vec![],
            type_: pph_type,
            value: pph_val,
        })?;

        // push-pop-tail : ∀ x v, vecTail (vecPush x v) = v   (ι)
        let ppt_type = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(list_t.clone());
            let concl = eq_list(Expr::app(vec_tail.clone(), push(&x, &v)), v.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, list_t.clone(), concl);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, nat.clone(), e))
        };
        let ppt_val = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(list_t.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, list_t.clone(), refl_list(v));
            b.finish(b.mk_lam(x_id, BinderInfo::Default, nat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_VEC_PUSH_POP_TAIL),
            level_params: vec![],
            type_: ppt_type,
            value: ppt_val,
        })?;

        Ok(())
    }

    /// Build the **HashMap give-back** anchor — a `HashMap<Nat,Nat>` with genuine
    /// presence/absence, modelled as a partial map `Nat → Option Nat` (`none` =
    /// absent). `mapInsert`/`mapRemove` branch on `Nat.beq` per key; `mapGet`
    /// applies. Proves (axiom-clean, via `Nat.beq_refl` + `congrArg`, the same
    /// idiom as the extensional store):
    ///
    ///   map_insertGet `mapGet (mapInsert m k v) k = some v`   (insert then get)
    ///   map_removeGet `mapGet (mapRemove m k) k = none`       (remove then get — gone)
    ///
    /// The remove/get law is the presence law a `HashMap` must satisfy (the key is
    /// genuinely absent after removal), beyond the total-store read-after-write.
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite (`Nat`, `Eq`, `Option`, `Nat.beq`) or
    /// a give-back declaration fails to admit / type-check.
    pub fn init_giveback_hashmap_refinement(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_eq()?; // congrArg
        self.init_option()?;
        self.register_nat_beq_lemmas()?; // Nat.beq, Nat.beq_refl, Bool, Bool.rec

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let u0 = Level::zero();
        let one = Level::succ(Level::zero());
        let opt_nat = Expr::app(
            Expr::const_(Name::from_string("Option"), vec![u0.clone()]),
            nat.clone(),
        );
        let map_t = Expr::arrow(nat.clone(), opt_nat.clone()); // Nat → Option Nat
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![one.clone()]); // motive → Option Nat : Sort 1
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let nat_beq_refl = Expr::const_(Name::from_string("Nat.beq_refl"), vec![]);
        let congr = Expr::const_(
            Name::from_string("congrArg"),
            vec![one.clone(), one.clone()],
        );
        let opt_some = Expr::const_(Name::from_string("Option.some"), vec![u0.clone()]);
        let opt_none = Expr::const_(Name::from_string("Option.none"), vec![u0]);
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);

        let some_e = |v: &Expr| Expr::apps(opt_some.clone(), [nat.clone(), v.clone()]);
        let none_e = Expr::app(opt_none.clone(), nat.clone());
        let beq = |a: &Expr, k: &Expr| Expr::apps(nat_beq.clone(), [a.clone(), k.clone()]);
        let eq_opt = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [opt_nat.clone(), l, r]);
        // optMotive := λ _ : Bool => Option Nat
        let opt_motive = |b: &EnvDeclBuilder| {
            let mut c = EnvDeclBuilder::child_of(b);
            let (m_id, _m) = c.fresh_local(bool_c.clone());
            c.finish_child(c.mk_lam(m_id, BinderInfo::Default, bool_c.clone(), opt_nat.clone()))
        };

        // mapGet : (Nat → Option Nat) → Nat → Option Nat := λ m k => m k
        let get_val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(map_t.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let e = b.mk_lam(
                k_id,
                BinderInfo::Default,
                nat.clone(),
                Expr::app(m.clone(), k),
            );
            b.finish(b.mk_lam(m_id, BinderInfo::Default, map_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_MAP_GET),
            level_params: vec![],
            type_: Expr::arrow(map_t.clone(), Expr::arrow(nat.clone(), opt_nat.clone())),
            value: get_val,
            is_reducible: true,
        })?;
        let map_get = Expr::const_(Name::from_string(GIVEBACK_MAP_GET), vec![]);

        // Build mapInsert / mapRemove: λ m k (payload) => λ a =>
        //   Bool.rec.{1} (λ_=>Option Nat) (m a) <hit> (Nat.beq a k)
        // where <hit> = `some v` for insert (needs the extra v binder) / `none` for remove.
        // mapInsert : (Nat→Option Nat) → Nat → Nat → (Nat→Option Nat)
        let insert_val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(map_t.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let cell = Expr::apps(
                bool_rec.clone(),
                [
                    opt_motive(&b),
                    Expr::app(m.clone(), a.clone()),
                    some_e(&v),
                    beq(&a, &k),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), cell);
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, map_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_MAP_INSERT),
            level_params: vec![],
            type_: Expr::arrow(
                map_t.clone(),
                Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), map_t.clone())),
            ),
            value: insert_val,
            is_reducible: true,
        })?;
        let map_insert = Expr::const_(Name::from_string(GIVEBACK_MAP_INSERT), vec![]);

        // mapRemove : (Nat→Option Nat) → Nat → (Nat→Option Nat)
        let remove_val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(map_t.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let cell = Expr::apps(
                bool_rec.clone(),
                [
                    opt_motive(&b),
                    Expr::app(m.clone(), a.clone()),
                    none_e.clone(),
                    beq(&a, &k),
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), cell);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, map_t.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_MAP_REMOVE),
            level_params: vec![],
            type_: Expr::arrow(map_t.clone(), Expr::arrow(nat.clone(), map_t.clone())),
            value: remove_val,
            is_reducible: true,
        })?;
        let map_remove = Expr::const_(Name::from_string(GIVEBACK_MAP_REMOVE), vec![]);

        let get = |m: &Expr, k: &Expr| Expr::apps(map_get.clone(), [m.clone(), k.clone()]);

        // insert_get : ∀ m k v, mapGet (mapInsert m k v) k = some v
        //   proof := λ m k v => congrArg Bool (Option Nat) (Nat.beq k k) true
        //              (λ b => Bool.rec (λ_=>Option Nat) (m k) (some v) b) (Nat.beq_refl k)
        let ig_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(map_t.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let ins = Expr::apps(map_insert.clone(), [m.clone(), k.clone(), v.clone()]);
            let concl = eq_opt(get(&ins, &k), some_e(&v));
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(m_id, BinderInfo::Default, map_t.clone(), e))
        };
        let ig_val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(map_t.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let f = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = c.fresh_local(bool_c.clone());
                let cell = Expr::apps(
                    bool_rec.clone(),
                    [
                        opt_motive(&c),
                        Expr::app(m.clone(), k.clone()),
                        some_e(&v),
                        bb.clone(),
                    ],
                );
                c.finish_child(c.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), cell))
            };
            let h = Expr::app(nat_beq_refl.clone(), k.clone());
            let body = Expr::apps(
                congr.clone(),
                [
                    bool_c.clone(),
                    opt_nat.clone(),
                    beq(&k, &k),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, map_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_MAP_INSERT_GET),
            level_params: vec![],
            type_: ig_type,
            value: ig_val,
        })?;

        // remove_get : ∀ m k, mapGet (mapRemove m k) k = none
        //   proof := λ m k => congrArg Bool (Option Nat) (Nat.beq k k) true
        //              (λ b => Bool.rec (λ_=>Option Nat) (m k) none b) (Nat.beq_refl k)
        let rg_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(map_t.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let rem = Expr::apps(map_remove.clone(), [m.clone(), k.clone()]);
            let concl = eq_opt(get(&rem, &k), none_e.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(m_id, BinderInfo::Default, map_t.clone(), e))
        };
        let rg_val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(map_t.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let f = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = c.fresh_local(bool_c.clone());
                let cell = Expr::apps(
                    bool_rec.clone(),
                    [
                        opt_motive(&c),
                        Expr::app(m.clone(), k.clone()),
                        none_e.clone(),
                        bb.clone(),
                    ],
                );
                c.finish_child(c.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), cell))
            };
            let h = Expr::app(nat_beq_refl.clone(), k.clone());
            let body = Expr::apps(
                congr.clone(),
                [
                    bool_c.clone(),
                    opt_nat.clone(),
                    beq(&k, &k),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(m_id, BinderInfo::Default, map_t.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_MAP_REMOVE_GET),
            level_params: vec![],
            type_: rg_type,
            value: rg_val,
        })?;

        Ok(())
    }

    /// Build the **operational step + bisimulation** anchor — the FIRST increment of
    /// the T-step tier. Reflects a small-step `step` over the store indexed by an
    /// OPERATION (modelled as `Option Nat`: `some v` = "write v", `none` = "incr"),
    /// dispatched by `Option.rec`:
    ///
    ///   gbStep s a op := match op with
    ///     | some v => gbUpdate s a v                       (write v at a)
    ///     | none   => gbUpdate s a (incrBack (s a))        (incr a)
    ///
    /// and proves the BISIMULATION laws — the give-back model agrees with each
    /// operational step's observable effect (axiom-clean, via `Option.rec` ι then
    /// the store `read-after-write` `congrArg`/`Nat.beq_refl` idiom):
    ///
    ///   step_writeReadsBack `gbLookup (gbStep s a (some v)) a = v`
    ///   step_incrReadsBack  `gbLookup (gbStep s a none) a = incrBack (gbLookup s a)`
    ///
    /// This is the operational tier in miniature: a step RELATION indexed by
    /// operations, with the give-back proved to simulate it per operation. (The full
    /// byte-addressed `Config`-level `step` + the four §3.5 metatheory lemmas are the
    /// larger follow-up, done in clean-rust-sem via the .lean route.)
    ///
    /// # Errors
    /// Returns [`EnvError`] if a prerequisite or a give-back declaration fails to
    /// admit / type-check.
    pub fn init_giveback_step_refinement(&mut self) -> Result<(), EnvError> {
        // init_giveback_refinement is not idempotent (re-admits backId); guard.
        if self
            .get_const(&Name::from_string(GIVEBACK_BACK_ID))
            .is_none()
        {
            self.init_giveback_refinement()?; // store: gbCond/gbUpdate/gbLookup + incrBack
        }
        self.init_option()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let u0 = Level::zero();
        let one = Level::succ(Level::zero());
        let store_ty = Expr::arrow(nat.clone(), nat.clone());
        let opt_nat = Expr::app(
            Expr::const_(Name::from_string("Option"), vec![u0.clone()]),
            nat.clone(),
        );
        let opt_some = Expr::const_(Name::from_string("Option.some"), vec![u0.clone()]);
        let opt_none = Expr::const_(Name::from_string("Option.none"), vec![u0.clone()]);
        let option_rec = Expr::const_(Name::from_string("Option.rec"), vec![one.clone(), u0]); // motive→Store : Sort 1
        let gb_update = Expr::const_(Name::from_string("RustSem.GiveBack.gbUpdate"), vec![]);
        let gb_lookup = Expr::const_(Name::from_string("RustSem.GiveBack.gbLookup"), vec![]);
        let gb_cond = Expr::const_(Name::from_string("RustSem.GiveBack.gbCond"), vec![]);
        let incr_back = Expr::const_(Name::from_string(GIVEBACK_INCR_BACK), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let nat_beq_refl = Expr::const_(Name::from_string("Nat.beq_refl"), vec![]);
        let congr = Expr::const_(
            Name::from_string("congrArg"),
            vec![one.clone(), one.clone()],
        );
        let eqc = Expr::const_(Name::from_string("Eq"), vec![one]);

        let some_e = |v: &Expr| Expr::apps(opt_some.clone(), [nat.clone(), v.clone()]);
        let none_e = Expr::app(opt_none.clone(), nat.clone());
        let update = |s: &Expr, a: &Expr, v: &Expr| {
            Expr::apps(gb_update.clone(), [s.clone(), a.clone(), v.clone()])
        };
        let lookup = |s: &Expr, a: &Expr| Expr::apps(gb_lookup.clone(), [s.clone(), a.clone()]);
        let beq = |x: &Expr, y: &Expr| Expr::apps(nat_beq.clone(), [x.clone(), y.clone()]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eqc.clone(), [nat.clone(), l, r]);

        // gbStep : Store → Nat → Option Nat → Store
        //   := λ s a op => Option.rec.{1,0} Nat (λ_=>Store)
        //                    (gbUpdate s a (incrBack (s a)))   -- none = incr
        //                    (λ v => gbUpdate s a v)           -- some v = write v
        //                    op
        let step_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let (op_id, op) = b.fresh_local(opt_nat.clone());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _m) = c.fresh_local(opt_nat.clone());
                c.finish_child(c.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    opt_nat.clone(),
                    store_ty.clone(),
                ))
            };
            let none_minor = update(
                &s,
                &a,
                &Expr::app(incr_back.clone(), Expr::app(s.clone(), a.clone())),
            );
            let some_minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (v_id, v) = c.fresh_local(nat.clone());
                c.finish_child(c.mk_lam(v_id, BinderInfo::Default, nat.clone(), update(&s, &a, &v)))
            };
            let body = Expr::apps(
                option_rec.clone(),
                [nat.clone(), motive, none_minor, some_minor, op.clone()],
            );
            let e = b.mk_lam(op_id, BinderInfo::Default, opt_nat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(GIVEBACK_STEP),
            level_params: vec![],
            type_: Expr::arrow(
                store_ty.clone(),
                Expr::arrow(nat.clone(), Expr::arrow(opt_nat.clone(), store_ty.clone())),
            ),
            value: step_val,
            is_reducible: true,
        })?;
        let gb_step = Expr::const_(Name::from_string(GIVEBACK_STEP), vec![]);
        let step = |s: &Expr, a: &Expr, op: &Expr| {
            Expr::apps(gb_step.clone(), [s.clone(), a.clone(), op.clone()])
        };

        // step_writeReadsBack : ∀ s a v, gbLookup (gbStep s a (some v)) a = v
        //   proof := λ s a v => congrArg Bool Nat (beq a a) true
        //              (λ b => gbCond b v (s a)) (Nat.beq_refl a)
        // (gbStep s a (some v) ι-reduces through Option.rec to gbUpdate s a v.)
        let write_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(lookup(&step(&s, &a, &some_e(&v)), &a), v.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        let write_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let f = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = c.fresh_local(bool_c.clone());
                let cell = Expr::apps(
                    gb_cond.clone(),
                    [bb.clone(), v.clone(), Expr::app(s.clone(), a.clone())],
                );
                c.finish_child(c.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), cell))
            };
            let h = Expr::app(nat_beq_refl.clone(), a.clone());
            let body = Expr::apps(
                congr.clone(),
                [
                    bool_c.clone(),
                    nat.clone(),
                    beq(&a, &a),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_STEP_WRITE),
            level_params: vec![],
            type_: write_type,
            value: write_val,
        })?;

        // step_incrReadsBack : ∀ s a, gbLookup (gbStep s a none) a = incrBack (gbLookup s a)
        //   proof := λ s a => congrArg Bool Nat (beq a a) true
        //              (λ b => gbCond b (incrBack (s a)) (s a)) (Nat.beq_refl a)
        let incr_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let rhs = Expr::app(incr_back.clone(), lookup(&s, &a));
            let concl = eq_nat(lookup(&step(&s, &a, &none_e), &a), rhs);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        let incr_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let new_v = Expr::app(incr_back.clone(), Expr::app(s.clone(), a.clone()));
            let f = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = c.fresh_local(bool_c.clone());
                let cell = Expr::apps(
                    gb_cond.clone(),
                    [bb.clone(), new_v.clone(), Expr::app(s.clone(), a.clone())],
                );
                c.finish_child(c.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), cell))
            };
            let h = Expr::app(nat_beq_refl.clone(), a.clone());
            let body = Expr::apps(
                congr.clone(),
                [
                    bool_c.clone(),
                    nat.clone(),
                    beq(&a, &a),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_STEP_INCR),
            level_params: vec![],
            type_: incr_type,
            value: incr_val,
        })?;

        // step_seqWriteLastWins : ∀ s a v1 v2,
        //   gbLookup (gbStep (gbStep s a (some v1)) a (some v2)) a = v2
        //   (last-write-wins across a 2-step trace; the first write is opaque under
        //   the second's congrArg — proof is the read-after-write idiom on step 2).
        let seq_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let (v2_id, v2) = b.fresh_local(nat.clone());
            let s1 = step(&s, &a, &some_e(&v1));
            let concl = eq_nat(lookup(&step(&s1, &a, &some_e(&v2)), &a), v2.clone());
            let e = b.mk_pi(v2_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(v1_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        let seq_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let (v1_id, v1) = b.fresh_local(nat.clone());
            let (v2_id, v2) = b.fresh_local(nat.clone());
            // value at `a` in the post-step-1 store (opaque to step 2's congrArg).
            let s1_at_a = Expr::app(step(&s, &a, &some_e(&v1)), a.clone());
            let f = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = c.fresh_local(bool_c.clone());
                let cell = Expr::apps(gb_cond.clone(), [bb.clone(), v2.clone(), s1_at_a.clone()]);
                c.finish_child(c.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), cell))
            };
            let h = Expr::app(nat_beq_refl.clone(), a.clone());
            let body = Expr::apps(
                congr.clone(),
                [
                    bool_c.clone(),
                    nat.clone(),
                    beq(&a, &a),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(v2_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(v1_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_STEP_SEQ),
            level_params: vec![],
            type_: seq_type,
            value: seq_val,
        })?;

        // §3.5 disjoint-Place frame (step level): a write step at `a` leaves every
        // OTHER address `a'` unchanged. Needs `Nat.beq_eq_false_of_ne` (gated module),
        // so this law is admitted under tests + the math-overlays feature (which the
        // trust-ir certifier enables); a bare default build omits it.
        #[cfg(any(test, feature = "math-overlays"))]
        {
            self.register_nat_beq_eq_false_of_ne()?;
            let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
            let nat_beq_false = Expr::const_(Name::from_string("Nat.beq_eq_false_of_ne"), vec![]);
            let false_c = Expr::const_(Name::from_string("False"), vec![]);
            let frame_type = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(store_ty.clone());
                let (a_id, a) = b.fresh_local(nat.clone());
                let (ap_id, ap) = b.fresh_local(nat.clone());
                let (v_id, v) = b.fresh_local(nat.clone());
                let hne_ty = Expr::arrow(eq_nat(ap.clone(), a.clone()), false_c.clone());
                let (hne_id, _hne) = b.fresh_local(hne_ty.clone());
                let concl = eq_nat(lookup(&step(&s, &a, &some_e(&v)), &ap), lookup(&s, &ap));
                let e = b.mk_pi(hne_id, BinderInfo::Default, hne_ty.clone(), concl);
                let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_pi(ap_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e))
            };
            let frame_val = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(store_ty.clone());
                let (a_id, a) = b.fresh_local(nat.clone());
                let (ap_id, ap) = b.fresh_local(nat.clone());
                let (v_id, v) = b.fresh_local(nat.clone());
                let hne_ty = Expr::arrow(eq_nat(ap.clone(), a.clone()), false_c.clone());
                let (hne_id, hne) = b.fresh_local(hne_ty.clone());
                let f = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (bb_id, bb) = c.fresh_local(bool_c.clone());
                    let cell = Expr::apps(
                        gb_cond.clone(),
                        [bb.clone(), v.clone(), Expr::app(s.clone(), ap.clone())],
                    );
                    c.finish_child(c.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), cell))
                };
                let h = Expr::apps(nat_beq_false.clone(), [ap.clone(), a.clone(), hne.clone()]);
                let body = Expr::apps(
                    congr.clone(),
                    [
                        bool_c.clone(),
                        nat.clone(),
                        beq(&ap, &a),
                        bfalse.clone(),
                        f,
                        h,
                    ],
                );
                let e = b.mk_lam(hne_id, BinderInfo::Default, hne_ty, body);
                let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_lam(ap_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), e);
                b.finish(b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(GIVEBACK_STEP_FRAME),
                level_params: vec![],
                type_: frame_type,
                value: frame_val,
            })?;
        }

        // §3.5 memory-level GIVE-BACK ROUND-TRIP: incrementing address a then giving back
        //   (writing the saved original gbLookup s a) reads back the original at a.
        //   := step_writeReadsBack (gbStep s a none) a (gbLookup s a)
        //   — the outer `some`-step reads back its written value, which is the saved original.
        let step_write = Expr::const_(Name::from_string(GIVEBACK_STEP_WRITE), vec![]);
        let rt_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let s1 = step(&s, &a, &none_e);
            let saved = lookup(&s, &a);
            let lhs = lookup(&step(&s1, &a, &some_e(&saved)), &a);
            let concl = eq_nat(lhs, lookup(&s, &a));
            let e = b.mk_pi(a_id, BinderInfo::Default, nat.clone(), concl);
            b.finish(b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        let rt_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let s1 = step(&s, &a, &none_e);
            let saved = lookup(&s, &a);
            let body = Expr::apps(step_write.clone(), [s1, a.clone(), saved]);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), body);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_STEP_ROUNDTRIP),
            level_params: vec![],
            type_: rt_type,
            value: rt_val,
        })?;

        Ok(())
    }

    /// Admit a real extensional STORE model (`Nat → Nat`) and the two fundamental
    /// memory laws — **read-after-write** and **frame / non-interference** — plus
    /// the **incr give-back-over-store** law: after `*x += 1`, reading `x` yields
    /// exactly `incrBack (old x)`, and every other cell is unchanged. Proved
    /// against `Nat.beq` via the existing `Nat.beq_refl` / `Nat.beq_eq_false_of_ne`
    /// lemmas (no `sorry`), admitted axiom-clean.
    ///
    /// Honest scope: an *extensional* store (a total `Nat → Nat`) — the standard
    /// PL-semantics store abstraction. Porting these laws to the byte-addressed
    /// `RustSem.Memory` assoc-list (clean-rust-sem) is the follow-up tier.
    fn declare_giveback_store(&mut self) -> Result<(), EnvError> {
        // Bring in Nat.beq + Nat.beq_refl (+ Bool, Bool.rec). Idempotent.
        // (The frame law's Nat.beq_eq_false_of_ne is registered inside the
        // cfg-gated frame block below — its module is math-overlays/test-gated.)
        self.register_nat_beq_lemmas()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let store_ty = Expr::arrow(nat.clone(), nat.clone()); // Nat → Nat
        let u1 = Level::succ(Level::zero());
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u1.clone()]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let beq = |x: &Expr, y: &Expr| Expr::apps(nat_beq.clone(), [x.clone(), y.clone()]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![u1.clone()]);
        let eq_nat = |l: Expr, r: Expr| Expr::apps(eq_const.clone(), [nat.clone(), l, r]);
        let incr_back = Expr::const_(Name::from_string(GIVEBACK_INCR_BACK), vec![]);

        // gbCond : Bool → Nat → Nat → Nat := λ cb t f => Bool.rec (λ _:Bool => Nat) f t cb
        // (false_case = f, true_case = t; so gbCond true t f ≡ t, gbCond false t f ≡ f).
        let gb_cond_ty = Expr::arrow(
            bool_c.clone(),
            Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
        );
        let gb_cond_val = {
            let mut b = EnvDeclBuilder::new();
            let (cb_id, cb) = b.fresh_local(bool_c.clone());
            let (t_id, t) = b.fresh_local(nat.clone());
            let (f_id, f) = b.fresh_local(nat.clone());
            let (mb_id, _mb) = b.fresh_local(bool_c.clone());
            let motive = b.mk_lam(mb_id, BinderInfo::Default, bool_c.clone(), nat.clone());
            let body = Expr::apps(bool_rec.clone(), [motive, f.clone(), t.clone(), cb.clone()]);
            let e = b.mk_lam(f_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(t_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(cb_id, BinderInfo::Default, bool_c.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("RustSem.GiveBack.gbCond"),
            level_params: vec![],
            type_: gb_cond_ty,
            value: gb_cond_val,
            is_reducible: true,
        })?;
        let gb_cond = Expr::const_(Name::from_string("RustSem.GiveBack.gbCond"), vec![]);

        // gbLookup : (Nat → Nat) → Nat → Nat := λ s k => s k
        let gb_lookup_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let e = b.mk_lam(
                k_id,
                BinderInfo::Default,
                nat.clone(),
                Expr::app(s.clone(), k),
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("RustSem.GiveBack.gbLookup"),
            level_params: vec![],
            type_: Expr::arrow(store_ty.clone(), Expr::arrow(nat.clone(), nat.clone())),
            value: gb_lookup_val,
            is_reducible: true,
        })?;
        let gb_lookup = Expr::const_(Name::from_string("RustSem.GiveBack.gbLookup"), vec![]);

        // gbUpdate : (Nat → Nat) → Nat → Nat → (Nat → Nat)
        //   := λ s k v => λ a => gbCond (Nat.beq a k) v (s a)
        let gb_update_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let (a_id, a) = b.fresh_local(nat.clone());
            let cell = Expr::apps(
                gb_cond.clone(),
                [beq(&a, &k), v.clone(), Expr::app(s.clone(), a.clone())],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, nat.clone(), cell);
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("RustSem.GiveBack.gbUpdate"),
            level_params: vec![],
            type_: Expr::arrow(
                store_ty.clone(),
                Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), store_ty.clone())),
            ),
            value: gb_update_val,
            is_reducible: true,
        })?;
        let gb_update = Expr::const_(Name::from_string("RustSem.GiveBack.gbUpdate"), vec![]);

        let lookup = |s: &Expr, k: &Expr| Expr::apps(gb_lookup.clone(), [s.clone(), k.clone()]);
        let update = |s: &Expr, k: &Expr, v: &Expr| {
            Expr::apps(gb_update.clone(), [s.clone(), k.clone(), v.clone()])
        };
        // congrArg.{1,1} Bool Nat a₁ a₂ f h : f a₁ = f a₂
        let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1.clone()]);
        let nat_beq_refl = Expr::const_(Name::from_string("Nat.beq_refl"), vec![]);

        // ── read-after-write : ∀ s k v, gbLookup (gbUpdate s k v) k = v ──────
        // proof := λ s k v => congrArg Bool Nat (Nat.beq k k) true
        //                       (λ b => gbCond b v (s k)) (Nat.beq_refl k)
        // (its type is defeq to the goal: gbCond true v (s k) ≡ v).
        let raw_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let concl = eq_nat(lookup(&update(&s, &k, &v), &k), v.clone());
            let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e);
            b.finish(e)
        };
        let raw_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(nat.clone());
            let (bb_id, bb) = b.fresh_local(bool_c.clone());
            let f = b.mk_lam(
                bb_id,
                BinderInfo::Default,
                bool_c.clone(),
                Expr::apps(
                    gb_cond.clone(),
                    [bb.clone(), v.clone(), Expr::app(s.clone(), k.clone())],
                ),
            );
            let h = Expr::app(nat_beq_refl.clone(), k.clone());
            let body = Expr::apps(
                congr_arg.clone(),
                [
                    bool_c.clone(),
                    nat.clone(),
                    beq(&k, &k),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_READ_AFTER_WRITE),
            level_params: vec![],
            type_: raw_type,
            value: raw_val,
        })?;

        // ── VALUE-POLYMORPHIC store + read-after-write : the give-back memory law
        // for ANY value type `α : Type` (Type 0). This is the generics foundation
        // — the same law a generic `fn f<T>(x: &mut T)` give-back needs. Defs take
        // α explicitly; the proof is the same congrArg + Nat.beq_refl (the key is
        // Nat; the value α is opaque), so it needs no value-type arithmetic.
        let type0 = Expr::sort(u1.clone()); // `Type` = `Sort 1`
                                            // gbCondP : (α : Type) → Bool → α → α → α := λ α cb t f => Bool.rec (λ _:Bool => α) f t cb
        let gb_cond_p_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let inner = Expr::arrow(
                bool_c.clone(),
                Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), alpha.clone())),
            );
            b.finish(b.mk_pi(a_id, BinderInfo::Default, type0.clone(), inner))
        };
        let gb_cond_p_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let (cb_id, cb) = b.fresh_local(bool_c.clone());
            let (t_id, t) = b.fresh_local(alpha.clone());
            let (f_id, f) = b.fresh_local(alpha.clone());
            let (mb_id, _mb) = b.fresh_local(bool_c.clone());
            let motive = b.mk_lam(mb_id, BinderInfo::Default, bool_c.clone(), alpha.clone());
            let body = Expr::apps(bool_rec.clone(), [motive, f.clone(), t.clone(), cb.clone()]);
            let e = b.mk_lam(f_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(t_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(cb_id, BinderInfo::Default, bool_c.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, type0.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("RustSem.GiveBack.gbCondP"),
            level_params: vec![],
            type_: gb_cond_p_ty,
            value: gb_cond_p_val,
            is_reducible: true,
        })?;
        let gb_cond_p = Expr::const_(Name::from_string("RustSem.GiveBack.gbCondP"), vec![]);

        // gbLookupP : (α : Type) → (Nat → α) → Nat → α := λ α s k => s k
        let gb_lookup_p_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let store_a = Expr::arrow(nat.clone(), alpha.clone());
            let inner = Expr::arrow(store_a, Expr::arrow(nat.clone(), alpha.clone()));
            b.finish(b.mk_pi(a_id, BinderInfo::Default, type0.clone(), inner))
        };
        let gb_lookup_p_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let store_a = Expr::arrow(nat.clone(), alpha.clone());
            let (s_id, s) = b.fresh_local(store_a.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let e = b.mk_lam(
                k_id,
                BinderInfo::Default,
                nat.clone(),
                Expr::app(s.clone(), k),
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, store_a, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, type0.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("RustSem.GiveBack.gbLookupP"),
            level_params: vec![],
            type_: gb_lookup_p_ty,
            value: gb_lookup_p_val,
            is_reducible: true,
        })?;
        let gb_lookup_p = Expr::const_(Name::from_string("RustSem.GiveBack.gbLookupP"), vec![]);

        // gbUpdateP : (α : Type) → (Nat → α) → Nat → α → (Nat → α)
        //   := λ α s k v => λ a => gbCondP α (Nat.beq a k) v (s a)
        let gb_update_p_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let store_a = Expr::arrow(nat.clone(), alpha.clone());
            let inner = Expr::arrow(
                store_a.clone(),
                Expr::arrow(nat.clone(), Expr::arrow(alpha.clone(), store_a)),
            );
            b.finish(b.mk_pi(a_id, BinderInfo::Default, type0.clone(), inner))
        };
        let gb_update_p_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let store_a = Expr::arrow(nat.clone(), alpha.clone());
            let (s_id, s) = b.fresh_local(store_a.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(alpha.clone());
            let (aa_id, aa) = b.fresh_local(nat.clone());
            let cell = Expr::apps(
                gb_cond_p.clone(),
                [
                    alpha.clone(),
                    beq(&aa, &k),
                    v.clone(),
                    Expr::app(s.clone(), aa.clone()),
                ],
            );
            let e = b.mk_lam(aa_id, BinderInfo::Default, nat.clone(), cell);
            let e = b.mk_lam(v_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, store_a, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, type0.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("RustSem.GiveBack.gbUpdateP"),
            level_params: vec![],
            type_: gb_update_p_ty,
            value: gb_update_p_val,
            is_reducible: true,
        })?;
        let gb_update_p = Expr::const_(Name::from_string("RustSem.GiveBack.gbUpdateP"), vec![]);

        // read_after_write_poly : ∀ (α : Type) (s : Nat → α) (k : Nat) (v : α),
        //   gbLookupP α (gbUpdateP α s k v) k = v
        // proof := λ α s k v => congrArg Bool α (Nat.beq k k) true
        //                         (λ b => gbCondP α b v (s k)) (Nat.beq_refl k)
        let poly_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let store_a = Expr::arrow(nat.clone(), alpha.clone());
            let (s_id, s) = b.fresh_local(store_a.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(alpha.clone());
            let lhs = Expr::apps(
                gb_lookup_p.clone(),
                [
                    alpha.clone(),
                    Expr::apps(
                        gb_update_p.clone(),
                        [alpha.clone(), s.clone(), k.clone(), v.clone()],
                    ),
                    k.clone(),
                ],
            );
            let concl = Expr::apps(eq_const.clone(), [alpha.clone(), lhs, v.clone()]);
            let e = b.mk_pi(v_id, BinderInfo::Default, alpha.clone(), concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, store_a, e);
            let e = b.mk_pi(a_id, BinderInfo::Default, type0.clone(), e);
            b.finish(e)
        };
        let poly_val = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, alpha) = b.fresh_local(type0.clone());
            let store_a = Expr::arrow(nat.clone(), alpha.clone());
            let (s_id, s) = b.fresh_local(store_a.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let (v_id, v) = b.fresh_local(alpha.clone());
            let (bb_id, bb) = b.fresh_local(bool_c.clone());
            let f = b.mk_lam(
                bb_id,
                BinderInfo::Default,
                bool_c.clone(),
                Expr::apps(
                    gb_cond_p.clone(),
                    [
                        alpha.clone(),
                        bb.clone(),
                        v.clone(),
                        Expr::app(s.clone(), k.clone()),
                    ],
                ),
            );
            let h = Expr::app(nat_beq_refl.clone(), k.clone());
            let body = Expr::apps(
                congr_arg.clone(),
                [
                    bool_c.clone(),
                    alpha.clone(),
                    beq(&k, &k),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(v_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, store_a, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, type0.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_READ_AFTER_WRITE_POLY),
            level_params: vec![],
            type_: poly_type,
            value: poly_val,
        })?;

        // ── frame : ∀ s k k' v, (k' = k → False) → gbLookup (gbUpdate s k v) k' = gbLookup s k' ──
        // proof := λ s k k' v hne => congrArg Bool Nat (Nat.beq k' k) false
        //                              (λ b => gbCond b v (s k')) (Nat.beq_eq_false_of_ne k' k hne)
        // frame needs `Nat.beq_eq_false_of_ne`, whose module is gated behind
        // `#[cfg(any(test, feature = "math-overlays"))]`. So the frame law is
        // admitted under tests and the math-overlays feature (which trust-ir's
        // certifier enables) — a bare default clean-kernel build still compiles,
        // it just omits the frame theorem.
        #[cfg(any(test, feature = "math-overlays"))]
        {
            self.register_nat_beq_eq_false_of_ne()?;
            let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
            let nat_beq_false = Expr::const_(Name::from_string("Nat.beq_eq_false_of_ne"), vec![]);
            let false_c = Expr::const_(Name::from_string("False"), vec![]);
            let frame_type = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(store_ty.clone());
                let (k_id, k) = b.fresh_local(nat.clone());
                let (kp_id, kp) = b.fresh_local(nat.clone());
                let (v_id, v) = b.fresh_local(nat.clone());
                let hne_ty = Expr::arrow(eq_nat(kp.clone(), k.clone()), false_c.clone());
                let (hne_id, _hne) = b.fresh_local(hne_ty.clone());
                let concl = eq_nat(lookup(&update(&s, &k, &v), &kp), lookup(&s, &kp));
                let e = b.mk_pi(hne_id, BinderInfo::Default, hne_ty.clone(), concl);
                let e = b.mk_pi(v_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_pi(kp_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e);
                b.finish(e)
            };
            let frame_val = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(store_ty.clone());
                let (k_id, k) = b.fresh_local(nat.clone());
                let (kp_id, kp) = b.fresh_local(nat.clone());
                let (v_id, v) = b.fresh_local(nat.clone());
                let hne_ty = Expr::arrow(eq_nat(kp.clone(), k.clone()), false_c.clone());
                let (hne_id, hne) = b.fresh_local(hne_ty.clone());
                let (bb_id, bb) = b.fresh_local(bool_c.clone());
                let f = b.mk_lam(
                    bb_id,
                    BinderInfo::Default,
                    bool_c.clone(),
                    Expr::apps(
                        gb_cond.clone(),
                        [bb.clone(), v.clone(), Expr::app(s.clone(), kp.clone())],
                    ),
                );
                // Nat.beq_eq_false_of_ne k' k hne : Nat.beq k' k = false
                let h = Expr::apps(nat_beq_false.clone(), [kp.clone(), k.clone(), hne.clone()]);
                let body = Expr::apps(
                    congr_arg.clone(),
                    [
                        bool_c.clone(),
                        nat.clone(),
                        beq(&kp, &k),
                        bfalse.clone(),
                        f,
                        h,
                    ],
                );
                let e = b.mk_lam(hne_id, BinderInfo::Default, hne_ty, body);
                let e = b.mk_lam(v_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_lam(kp_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
                let e = b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(GIVEBACK_FRAME),
                level_params: vec![],
                type_: frame_type,
                value: frame_val,
            })?;
        }

        // ── incr_store : ∀ s k, gbLookup (gbUpdate s k (incrBack (gbLookup s k))) k = incrBack (gbLookup s k) ──
        // The give-back over a real store: after `*x += 1`, reading x yields incrBack(old x).
        let incr_store_type = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let new_v = Expr::app(incr_back.clone(), lookup(&s, &k));
            let concl = eq_nat(lookup(&update(&s, &k, &new_v), &k), new_v.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), concl);
            let e = b.mk_pi(s_id, BinderInfo::Default, store_ty.clone(), e);
            b.finish(e)
        };
        let incr_store_val = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(store_ty.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let new_v = Expr::app(incr_back.clone(), lookup(&s, &k));
            let (bb_id, bb) = b.fresh_local(bool_c.clone());
            let f = b.mk_lam(
                bb_id,
                BinderInfo::Default,
                bool_c.clone(),
                Expr::apps(
                    gb_cond.clone(),
                    [bb.clone(), new_v.clone(), Expr::app(s.clone(), k.clone())],
                ),
            );
            let h = Expr::app(nat_beq_refl.clone(), k.clone());
            let body = Expr::apps(
                congr_arg.clone(),
                [
                    bool_c.clone(),
                    nat.clone(),
                    beq(&k, &k),
                    btrue.clone(),
                    f,
                    h,
                ],
            );
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::Default, store_ty.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(GIVEBACK_INCR_STORE),
            level_params: vec![],
            type_: incr_store_type,
            value: incr_store_val,
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;

    #[test]
    fn giveback_anchor_admits_axiom_clean_theorem() {
        // Establish the prerequisites first (Nat + Eq bring their own foundational
        // axioms, e.g. propext); the claim is that the give-back declarations add
        // ZERO further domain axioms. init_* are idempotent, so the subsequent
        // init_giveback_refinement only adds backId + the round-trip law.
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_refinement()
            .expect("give-back refinement anchor should build");

        let thm = Name::from_string(GIVEBACK_BACK_ID_ROUNDTRIPS);
        let info = env
            .get_const(&thm)
            .expect("round-trip theorem must be present");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "the round-trip law must be a proof-carrying Theorem (re-checkable)"
        );
        // The POLYMORPHIC identity round-trip must also be present + per-theorem clean.
        let poly = Name::from_string(GIVEBACK_BACK_ID_POLY_ROUNDTRIPS);
        assert_eq!(
            env.get_const(&poly)
                .expect("polymorphic round-trip theorem must be present")
                .kind,
            ConstantKind::Theorem,
            "backIdP_roundTrips must be a proof-carrying Theorem"
        );
        assert!(
            env.axiom_deps(&poly).unwrap_or_default().is_empty(),
            "backIdP_roundTrips must be per-theorem axiom-clean"
        );
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the give-back round-trip laws must be axiom-clean"
        );
    }

    #[test]
    fn incr_giveback_lens_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_refinement()
            .expect("give-back anchor (incl. incr lens laws) should build");

        // incrBack and its composition laws are present, proof-carrying, and
        // proved by genuine symbolic ι-reduction of Nat.add (not literal arith).
        for thm in [
            GIVEBACK_INCR_STEP,
            GIVEBACK_INCR_COMPOSES,
            GIVEBACK_INCR_THRICE,
            GIVEBACK_ADD_K_STEP,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the incr give-back lens-composition laws must be axiom-clean"
        );
    }

    #[test]
    fn giveback_store_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_refinement()
            .expect("give-back anchor (incl. store laws) should build");

        // The two fundamental memory laws + the incr give-back-over-store law are
        // present, proof-carrying, and proved (no sorry) against Nat.beq.
        for thm in [
            GIVEBACK_READ_AFTER_WRITE,
            GIVEBACK_READ_AFTER_WRITE_POLY,
            GIVEBACK_FRAME,
            GIVEBACK_INCR_STORE,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the store read-after-write / frame / incr laws must be axiom-clean"
        );
    }

    #[test]
    fn incr_u32_wraparound_admits_and_is_per_theorem_axiom_clean() {
        let mut env = Environment::new();
        // The .expect proves the wraparound TYPE-CHECKED: the kernel reduced
        // incrBackU32 (u32::MAX) to UInt32.mk 0 (Nat.add then Nat.mod 2^32) and
        // accepted Eq.refl — genuine u32 overflow (false over Nat).
        env.init_giveback_u32_refinement()
            .expect("u32 wraparound anchor should build (incr(u32::MAX) = 0 by reduction)");

        let thm = Name::from_string(GIVEBACK_INCR_U32_WRAPS);
        let info = env
            .get_const(&thm)
            .expect("wraparound theorem must be present");
        assert_eq!(info.kind, ConstantKind::Theorem);

        // PER-THEOREM axiom-clean: although the env also admits UInt32/Fin
        // machinery (which carries a few domain axioms), the wraparound proof's
        // own transitive closure uses only constructors/defs (UInt32.mk/.val,
        // Nat.add/Nat.mod, Eq.refl) — no domain axioms. This is exactly what the
        // CleanCic per-theorem re-check verifies.
        let deps = env.axiom_deps(&thm).unwrap_or_default();
        assert!(
            deps.is_empty(),
            "incrBackU32_wraps must be per-theorem axiom-clean, got: {deps:?}"
        );
    }

    #[test]
    fn aggregate_giveback_lens_laws_admit_axiom_clean() {
        // Prereqs (Nat/Eq/Prod) bring their own foundational axioms; the claim is
        // the aggregate give-back laws add ZERO domain axioms (Prod is a pure
        // inductive; the laws are proved by Eq.refl over δ + proj-ι + structure-eta).
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_prod().expect("Prod");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_aggregate_refinement()
            .expect("aggregate give-back anchor should build (struct-field &mut lens laws)");

        // All four lens laws + the composed incr law are present and proof-carrying.
        for thm in [
            GIVEBACK_AGG_PUT_GET,
            GIVEBACK_AGG_GET_PUT,
            GIVEBACK_AGG_FRAME,
            GIVEBACK_AGG_PUT_PUT,
            GIVEBACK_AGG_INCR,
            GIVEBACK_AGG_FST_LENS_P_PUTGET,
            GIVEBACK_AGG_FST_LENS_P_GETPUT,
            GIVEBACK_AGG_FST_LENS_P_FRAME,
            GIVEBACK_AGG_SND_LENS_P_PUTGET,
            GIVEBACK_AGG_SND_LENS_P_GETPUT,
            GIVEBACK_AGG_SND_LENS_P_FRAME,
            GIVEBACK_AGG_LENS_COMPOSE_PUTGET,
            GIVEBACK_AGG_LENS_COMPOSE_GETPUT,
            GIVEBACK_AGG_NEST_LENS_GETPUT,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            // PER-THEOREM axiom-clean: each law's own transitive closure is empty
            // (only constructors/projections/defs + Eq.refl) — what the CleanCic
            // per-theorem re-check enforces.
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the aggregate give-back lens laws must add zero domain axioms"
        );
    }

    /// The get-put round-trip is the discriminating law: it holds ONLY because the
    /// backward function reconstructs the WHOLE aggregate (framed sibling included)
    /// and the kernel's structure-eta closes `Prod.mk p.fst p.snd = p`. Guard that
    /// it is genuinely the round-trip statement over `Prod Nat Nat`, not a trivial
    /// reflexivity on a scalar.
    #[test]
    fn aggregate_get_put_is_real_roundtrip_over_pair() {
        let mut env = Environment::new();
        env.init_giveback_aggregate_refinement()
            .expect("aggregate give-back anchor should build");
        let info = env
            .get_const(&Name::from_string(GIVEBACK_AGG_GET_PUT))
            .expect("get-put law present");
        // The conclusion compares two `Prod Nat Nat` values (the round-trip), so
        // the statement mentions Prod — a scalar-only reflexivity would not.
        let printed = format!("{:?}", info.type_);
        assert!(
            printed.contains("Prod"),
            "get-put must be the aggregate round-trip over Prod, got: {printed}"
        );
    }

    #[test]
    fn enum_giveback_case_analysis_laws_admit_axiom_clean() {
        // Prereqs (Nat/Eq/Option) bring foundational axioms; the claim is the
        // sum-type give-back laws add ZERO domain axioms (Option is a pure
        // inductive; the ∀o laws are proved by Option.rec — case analysis — and
        // the per-variant laws by Eq.refl).
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_option().expect("Option");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_enum_refinement()
            .expect("enum give-back anchor should build (Option.rec case-analysis laws)");

        for thm in [
            GIVEBACK_OPT_FRAME_NONE,
            GIVEBACK_OPT_SET_SOME,
            GIVEBACK_OPT_PUT_PUT,
            GIVEBACK_OPT_ROUNDTRIP,
            GIVEBACK_OPT_INCR_SOME,
            GIVEBACK_OPT_TAGGED_BRIDGE,
            GIVEBACK_SUM_ROUNDTRIP,
            GIVEBACK_SUM_MAP_ROUNDTRIP,
            GIVEBACK_OPT_MAP_ROUNDTRIP,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the sum-type give-back laws must add zero domain axioms"
        );
    }

    /// put-put and round-trip are the discriminating sum-type laws: they quantify
    /// over an OPAQUE `o : Option Nat` and so cannot be proved by `Eq.refl` (no
    /// eta for sums) — they must invoke `Option.rec` to split per variant. Guard
    /// that the round-trip proof TERM genuinely uses the recursor.
    #[test]
    fn enum_roundtrip_proof_uses_the_recursor() {
        let mut env = Environment::new();
        env.init_giveback_enum_refinement()
            .expect("enum give-back anchor should build");
        let info = env
            .get_const(&Name::from_string(GIVEBACK_OPT_ROUNDTRIP))
            .expect("round-trip law present");
        let proof = info
            .value
            .as_ref()
            .expect("round-trip is a proof-carrying Theorem");
        let printed = format!("{proof:?}");
        // The recursor's name renders structurally in Debug as `…"Option"…, "rec"…`
        // (not the dotted literal). A refl-only proof would contain neither — it
        // would be `Lam(_, App(App(Eq.refl …) …))`. Require the recursor segment.
        assert!(
            printed.contains("\"rec\"") && printed.contains("\"Option\""),
            "the ∀o round-trip must be proved by case analysis (Option.rec), got: {printed}"
        );
    }

    #[test]
    fn list_giveback_recursive_laws_admit_axiom_clean() {
        // Prereqs (Nat/Eq/List) bring foundational axioms; the claim is the
        // recursive give-back laws add ZERO domain axioms (List is a pure
        // inductive; the round-trip is proved by List.rec structural induction —
        // congrArg + the recursion hypothesis — and the cons laws by Eq.refl).
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_list().expect("List");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_list_refinement()
            .expect("recursive (list) give-back anchor should build (List.rec induction)");

        for thm in [
            GIVEBACK_LIST_SELF_CONS,
            GIVEBACK_LIST_ROUNDTRIP,
            GIVEBACK_LIST_INCR_CONS,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the recursive give-back laws must add zero domain axioms"
        );
    }

    /// The recursive round-trip `∀ l, listSelf l = l` is the discriminating law:
    /// over an OPAQUE arbitrarily-deep `l` it requires STRUCTURAL INDUCTION, so the
    /// proof TERM must invoke `List.rec` AND consume the recursion hypothesis via
    /// `congrArg` (a refl-only proof is impossible). Guard both appear.
    #[test]
    fn list_roundtrip_proof_uses_recursor_and_congr() {
        let mut env = Environment::new();
        env.init_giveback_list_refinement()
            .expect("recursive give-back anchor should build");
        let info = env
            .get_const(&Name::from_string(GIVEBACK_LIST_ROUNDTRIP))
            .expect("round-trip law present");
        let proof = info
            .value
            .as_ref()
            .expect("round-trip is a proof-carrying Theorem");
        let printed = format!("{proof:?}");
        assert!(
            printed.contains("\"rec\"") && printed.contains("\"List\""),
            "the ∀l round-trip must use structural induction (List.rec), got: {printed}"
        );
        assert!(
            printed.contains("congrArg"),
            "the round-trip must lift the recursion hypothesis via congrArg, got: {printed}"
        );
    }

    #[test]
    fn split_disjoint_borrow_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_prod().expect("Prod");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_split_refinement()
            .expect("disjoint-borrow (split_at_mut) anchor should build");

        for thm in [
            GIVEBACK_SPLIT_DISJOINT01,
            GIVEBACK_SPLIT_DISJOINT10,
            GIVEBACK_SPLIT_COMMUTE,
            GIVEBACK_SPLIT_COMBINE,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the disjoint-borrow give-back laws must add zero domain axioms"
        );
    }

    /// The commute law is the separation witness: two live `&mut`s into one value
    /// are sound exactly when their give-backs do not interfere, so recombination
    /// order is irrelevant. Guard it is genuinely an equality between two distinct
    /// nestings (`splitBack1 (splitBack0 …)` vs `splitBack0 (splitBack1 …)`).
    #[test]
    fn split_commute_is_real_order_independence() {
        let mut env = Environment::new();
        env.init_giveback_split_refinement()
            .expect("disjoint-borrow anchor should build");
        let info = env
            .get_const(&Name::from_string(GIVEBACK_SPLIT_COMMUTE))
            .expect("commute law present");
        let printed = format!("{:?}", info.type_);
        // Both backward functions appear on the two sides of the equation.
        assert!(
            printed.contains("splitBack0") && printed.contains("splitBack1"),
            "commute must relate both disjoint give-backs, got: {printed}"
        );
    }

    #[test]
    fn cond_giveback_control_flow_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_bool().expect("Bool");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_cond_refinement()
            .expect("control-flow give-back anchor should build (Bool.rec branch laws)");

        for thm in [
            GIVEBACK_COND_TRUE,
            GIVEBACK_COND_FALSE,
            GIVEBACK_COND_SELF,
            GIVEBACK_COND_PAIR_TRUE,
            GIVEBACK_COND_PAIR_FALSE,
            GIVEBACK_COND_POLY_TRUE,
            GIVEBACK_COND_POLY_FALSE,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the control-flow give-back laws must add zero domain axioms"
        );
    }

    /// The `∀ c` no-op law is the discriminating control-flow law: over an OPAQUE
    /// runtime flag it requires CASE ANALYSIS, so the proof TERM must invoke
    /// `Bool.rec` (a per-branch refl is not enough for the quantified statement).
    #[test]
    fn cond_self_proof_uses_bool_case_analysis() {
        let mut env = Environment::new();
        env.init_giveback_cond_refinement()
            .expect("control-flow give-back anchor should build");
        let info = env
            .get_const(&Name::from_string(GIVEBACK_COND_SELF))
            .expect("cond_self law present");
        let proof = info
            .value
            .as_ref()
            .expect("cond_self is a proof-carrying Theorem");
        let printed = format!("{proof:?}");
        assert!(
            printed.contains("\"rec\"") && printed.contains("\"Bool\""),
            "the ∀c no-op law must use Bool.rec case analysis, got: {printed}"
        );
    }

    #[test]
    fn nested_giveback_two_level_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_prod().expect("Prod");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_nested_refinement()
            .expect("nested give-back anchor should build (two-level structure-eta)");

        for thm in [
            GIVEBACK_NEST_PUT_GET,
            GIVEBACK_NEST_GET_PUT,
            GIVEBACK_NEST_FRAME_INNER,
            GIVEBACK_NEST_FRAME_OUTER,
            GIVEBACK_NEST_INCR,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the nested give-back laws must add zero domain axioms"
        );
    }

    #[test]
    fn loop_giveback_roundtrip_admits_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_list().expect("List");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_loop_refinement()
            .expect("loop give-back anchor should build (List.rec induction + Nat.pred ι)");

        for thm in [
            GIVEBACK_LOOP_FWD_CONS,
            GIVEBACK_LOOP_ROUNDTRIP,
            GIVEBACK_LOOP_MAP_ROUNDTRIP,
            GIVEBACK_LOOP_MAP_T_ROUNDTRIP,
            GIVEBACK_LOOP_NOT_NOT,
            GIVEBACK_LOOP_BOOLNOT_ROUNDTRIP,
            GIVEBACK_LOOP_PAIRINCR_ROUNDTRIP,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the loop give-back laws must add zero domain axioms"
        );
    }

    /// The loop round-trip `∀ l, loopBack (loopFwd l) = l` quantifies over an
    /// OPAQUE list of ANY length, so it requires STRUCTURAL INDUCTION: the proof
    /// TERM must invoke `List.rec` and lift the recursion hypothesis via `congrArg`
    /// (a finite unroll cannot prove it). Guard both appear.
    #[test]
    fn loop_roundtrip_proof_uses_induction() {
        let mut env = Environment::new();
        env.init_giveback_loop_refinement()
            .expect("loop give-back anchor should build");
        let info = env
            .get_const(&Name::from_string(GIVEBACK_LOOP_ROUNDTRIP))
            .expect("loop round-trip law present");
        let proof = info.value.as_ref().expect("proof-carrying Theorem");
        let printed = format!("{proof:?}");
        assert!(
            printed.contains("\"rec\"")
                && printed.contains("\"List\"")
                && printed.contains("congrArg"),
            "the ∀l loop round-trip must use List.rec induction + congrArg, got: {printed}"
        );
    }

    #[test]
    fn generic_giveback_instantiations_admit_axiom_clean() {
        // The generic give-back law specializes to concrete T (Nat/Bool/Prod) by
        // application — one proof covers every T (monomorphization made sound).
        let mut env = Environment::new();
        env.init_giveback_refinement().expect("base anchor");
        env.init_bool().expect("Bool");
        env.init_prod().expect("Prod");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_generics_refinement()
            .expect("generic give-back anchor should build (poly law instantiated)");

        for thm in [GIVEBACK_GEN_NAT, GIVEBACK_GEN_BOOL, GIVEBACK_GEN_PROD] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            // The instance's closure equals the (axiom-clean) generic law's.
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "instantiating the generic give-back law must add zero domain axioms"
        );
    }

    #[test]
    fn closure_giveback_env_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_prod().expect("Prod");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_closure_refinement()
            .expect("closure give-back anchor should build (env reconstruction)");

        for thm in [
            GIVEBACK_CLO_CALL_EFFECT,
            GIVEBACK_CLO_FRAME,
            GIVEBACK_CLO_NOOP,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the closure give-back laws must add zero domain axioms"
        );
    }

    #[test]
    fn trait_giveback_dispatch_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_prod().expect("Prod");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_trait_refinement()
            .expect("trait give-back anchor should build (vtable dyn dispatch)");

        for thm in [
            GIVEBACK_TRAIT_RESOLVES,
            GIVEBACK_TRAIT_ID,
            GIVEBACK_TRAIT_INCR,
            GIVEBACK_ASSOC_INCR,
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the trait give-back laws must add zero domain axioms"
        );
    }

    #[test]
    fn vec_giveback_push_pop_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_list().expect("List");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_vec_refinement()
            .expect("Vec give-back anchor should build (push/pop round-trip)");

        for thm in [GIVEBACK_VEC_PUSH_POP_HEAD, GIVEBACK_VEC_PUSH_POP_TAIL] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the Vec give-back laws must add zero domain axioms"
        );
    }

    #[test]
    fn hashmap_giveback_presence_laws_admit_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_eq().expect("Eq");
        env.init_option().expect("Option");
        env.register_nat_beq_lemmas().expect("Nat.beq");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_hashmap_refinement()
            .expect("HashMap give-back anchor should build (insert/remove + get)");

        for thm in [GIVEBACK_MAP_INSERT_GET, GIVEBACK_MAP_REMOVE_GET] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the HashMap give-back laws must add zero domain axioms"
        );
    }

    #[test]
    fn step_bisimulation_laws_admit_axiom_clean() {
        // The operational-step bisimulation: the give-back model agrees with each
        // operational step (write / incr) over the store, per operation.
        let mut env = Environment::new();
        env.init_giveback_refinement().expect("store anchor");
        env.init_option().expect("Option");
        let before = env.soundness_report().total_domain_axioms;

        env.init_giveback_step_refinement()
            .expect("operational step + bisimulation anchor should build");

        for thm in [
            GIVEBACK_STEP_WRITE,
            GIVEBACK_STEP_INCR,
            GIVEBACK_STEP_SEQ,
            GIVEBACK_STEP_ROUNDTRIP,
            GIVEBACK_STEP_FRAME, // present under cfg(test)
        ] {
            let info = env
                .get_const(&Name::from_string(thm))
                .unwrap_or_else(|| panic!("{thm} must be present in the anchor env"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{thm} must be a proof-carrying Theorem (kernel-re-checkable)"
            );
            let deps = env.axiom_deps(&Name::from_string(thm)).unwrap_or_default();
            assert!(
                deps.is_empty(),
                "{thm} must be per-theorem axiom-clean, got: {deps:?}"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the step bisimulation laws must add zero domain axioms"
        );
    }
}
