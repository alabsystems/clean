// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic identity — "is this the same object in a different form?"
//!
//! Cake owns the corpus's notion of *sameness*. A purely structural digest (alpha
//! equivalence over de Bruijn terms) misses re-encodings: `a + b` vs `b + a` when
//! defeq, a folded definition vs its unfolding, eta-variants, numeral normalisation.
//! Those would each be counted as "novel" and miss each other in search. This module
//! is the tiered fix.
//!
//! ## Tier 1 — definitional equality (sound, decidable)
//!
//! In type theory the principled notion of "the same object" is **definitional
//! equality** (defeq): two statements are the same iff their types are defeq (a proof
//! of one is a proof of the other). Defeq is decidable — the kernel decides it via
//! [`clean_kernel::tc::TypeChecker::is_def_eq`].
//!
//! We expose it as a **two-part** primitive, because a single hash cannot be a
//! *complete* canonical form for defeq in general (normalisation can be unbounded):
//!
//! * [`defeq_canonical_digest`] — normalise the statement to a head/▸children normal
//!   form via the kernel ([`whnf`](clean_kernel::tc::TypeChecker::whnf): β, η, δ on
//!   reducibles, ι, ζ, proj) under a fuel bound, then hash. It is a **one-directional
//!   bucketing key, NOT a sound decision** — it groups likely-equal candidates to
//!   *dramatically limit the search space*; `same_object` makes the actual call. The
//!   safe reading is *equal digest ⇒ run `is_def_eq`*, never *equal digest ⇒ defeq*.
//!   Three documented incompletenesses make a digest **miss** possible (a miss is
//!   "unknown", never "distinct"): (a) fuel exhaustion — recorded via
//!   [`SemanticIdentity::complete`]`= false`; (b) **non-core ExprKind variants**
//!   (`Squash`/`Cubical*`/`ZFC*`) are left as opaque heads — their subterms are not
//!   normalised (these modes do not occur in the Lean4/Mathlib corpus this targets);
//!   (c) the flat encoder's `BigNat` fallback (see `flat_digest`) hashes a debug form,
//!   so a term that hits it will not bucket with a defeq term that does not. Under
//!   `complete = true`, no encoder fallback, and the core fragment, equal digests are
//!   defeq — but `same_object` is always the arbiter.
//! * [`same_object`] — `is_def_eq`, the kernel's **sound decision**. Run it to
//!   *confirm* sameness within a digest bucket. Bucketing makes this O(bucket), not
//!   O(corpus).
//!
//! ## Tier 1.5 — canonical-rewrite digest (deterministic, best-effort) — LANDED
//!
//! [`rewrite_canonical_digest`] (env-dependent: defeq-normalise then canonicalise) and
//! [`structural_rewrite_digest`] (env-free: canonicalise only — the corpus-scale key) apply
//! a confluent, terminating commutative-operand canonicalisation ([`canonicalize_comm`])
//! before hashing, collapsing forms defeq misses (`a + b` / `b + a`, `P ∧ Q` / `Q ∧ P`)
//! while staying a deterministic hash. Honestly incomplete; never a soundness claim — a
//! collision is a *bucket candidate* (confirm via [`same_object`] / a `proved-iff` cert).
//!
//! ## Tier 2 — the lineage graph (strong evidence, not proof) — LANDED
//!
//! [`crate::lineage`] is the accumulating equivalence graph whose nodes are digests and
//! whose edges are graded *identity hints* carrying provenance + trust:
//! `defeq` / `rewrite-canonical` (deterministic), **`proved-iff:<cert>`** (a
//! kernel-checked `A ↔ B` — the only *sound* logical-equivalence link), `import-alias`
//! (cross-system provenance), `conjectured` (low trust, never auto-trusted). Union-find
//! over the edges yields equivalence classes that bound where uniqueness/search must
//! even look; a later `proved-iff` upgrades a `conjectured` edge, so the corpus
//! converges toward the undecidable logical tier without ever *claiming* it.

use clean_kernel::expr::ExprKind;
use clean_kernel::flat::FlatBuilder;
use clean_kernel::tc::TypeChecker;
use clean_kernel::{Expr, Name};

use serde::{Deserialize, Serialize};

/// Default normalisation fuel — total reduction steps before [`normalize_nf`] gives
/// up and records the result as incomplete. Statement *types* (Props) normalise well
/// under this; the bound only guards pathological/divergent terms.
pub const DEFAULT_NORMALIZE_FUEL: u32 = 200_000;

/// The Tier-1 semantic identity of a statement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticIdentity {
    /// `blake3:<hex>` over the normalised (defeq-canonical) form. A sound bucketing
    /// key: equal digests ⇒ candidates to confirm with [`same_object`].
    pub canonical_digest: String,
    /// `blake3:<hex>` over the *un-normalised* term (alpha/structural identity).
    /// Always exact; the floor when normalisation is incomplete.
    pub structural_digest: String,
    /// Tier-1.5 `blake3:<hex>` over the defeq normal form *after* canonical commutative-
    /// operand reordering. A **stronger bucketing key** than `canonical_digest`: collapses
    /// propositionally-equal forms (e.g. `a + b` / `b + a`, `P ∧ Q` / `Q ∧ P`) that are not
    /// defeq. Deterministic, NOT a soundness claim — a collision means "candidate", to be
    /// confirmed by `same_object` (defeq) or a `proved-iff` certificate (logical).
    pub rewrite_digest: String,
    /// Did normalisation finish within fuel? When `false`, `canonical_digest` is a
    /// partial normal form — still a valid bucket, but two defeq terms are less likely
    /// to share it, so treat misses as "unknown", not "distinct".
    pub complete: bool,
}

/// Raw 32-byte blake3 of a kernel expression's deterministic flat encoding.
/// `add_kernel_expr` only fails on encoder-internal limits; fall back to the Debug form so
/// a digest is always produced (distinct terms still differ).
fn flat_raw(e: &Expr) -> [u8; 32] {
    let mut builder = FlatBuilder::new();
    if builder.add_kernel_expr(e).is_err() {
        return *blake3::hash(format!("{e:?}").as_bytes()).as_bytes();
    }
    let mut bytes = Vec::new();
    if builder.write_to(&mut bytes).is_err() {
        return *blake3::hash(format!("{e:?}").as_bytes()).as_bytes();
    }
    *blake3::hash(&bytes).as_bytes()
}

/// Hash a kernel expression's deterministic flat encoding to `blake3:<hex>`.
fn flat_digest(e: &Expr) -> String {
    format!("blake3:{}", blake3::Hash::from(flat_raw(e)).to_hex())
}

struct NormCtx {
    fuel: u32,
    complete: bool,
}

/// Recursively reduce `e` to normal form: weak-head-normalise, then normalise the
/// subterms of the resulting head (function spine, binder domain + body, projection
/// scrutinee). Reductions under binders treat the bound variable as a stuck term, so
/// the result is the open normal form. Fuel-bounded; sets `ctx.complete = false` if
/// the bound is hit anywhere.
fn normalize_nf(tc: &TypeChecker, e: &Expr, ctx: &mut NormCtx) -> Expr {
    if ctx.fuel == 0 {
        ctx.complete = false;
        return e.clone();
    }
    ctx.fuel -= 1;

    let head = tc.whnf(e);
    match head.kind() {
        ExprKind::App(f, a) => {
            let nf = normalize_nf(tc, f, ctx);
            let na = normalize_nf(tc, a, ctx);
            Expr::app(nf, na)
        }
        ExprKind::Lam(bd, ty, body) => {
            let nty = normalize_nf(tc, ty, ctx);
            let nbody = normalize_nf(tc, body, ctx);
            Expr::lam(*bd, nty, nbody)
        }
        ExprKind::Pi(bd, ty, body) => {
            let nty = normalize_nf(tc, ty, ctx);
            let nbody = normalize_nf(tc, body, ctx);
            Expr::pi(*bd, nty, nbody)
        }
        ExprKind::Proj(name, idx, s) => {
            let ns = normalize_nf(tc, s, ctx);
            Expr::proj(name.clone(), *idx, ns)
        }
        ExprKind::Let(name, ty, val, body, non_dep) => {
            // whnf normally ζ-reduces lets away; if one survives, normalise its parts.
            let nty = normalize_nf(tc, ty, ctx);
            let nval = normalize_nf(tc, val, ctx);
            let nbody = normalize_nf(tc, body, ctx);
            Expr::let_named(name.clone(), nty, nval, nbody, *non_dep)
        }
        ExprKind::MData(_, inner) => normalize_nf(tc, inner, ctx),
        // Const, Sort, Lit, BVar, FVar, SProp, … are already normal heads.
        _ => head,
    }
}

/// Compute the Tier-1 [`SemanticIdentity`] of `expr` in `tc`'s environment.
#[must_use]
pub fn defeq_canonical_digest(tc: &TypeChecker, expr: &Expr) -> SemanticIdentity {
    defeq_canonical_digest_fueled(tc, expr, DEFAULT_NORMALIZE_FUEL)
}

/// [`defeq_canonical_digest`] with an explicit fuel bound. Public: the graduation gate's
/// `--score-defeq` path calls it cross-crate with a small bound to keep the expensive
/// kernel normalisation from hanging on heavy mathlib-Real statements.
#[must_use]
pub fn defeq_canonical_digest_fueled(tc: &TypeChecker, expr: &Expr, fuel: u32) -> SemanticIdentity {
    let structural_digest = flat_digest(expr);
    let mut ctx = NormCtx {
        fuel,
        complete: true,
    };
    let nf = normalize_nf(tc, expr, &mut ctx);
    SemanticIdentity {
        canonical_digest: flat_digest(&nf),
        structural_digest,
        rewrite_digest: flat_digest(&canonicalize_comm(&nf)),
        complete: ctx.complete,
    }
}

/// The Tier-1.5 digest alone: defeq-normalise then canonical-rewrite, then hash.
#[must_use]
pub(crate) fn rewrite_canonical_digest(tc: &TypeChecker, expr: &Expr) -> String {
    let mut ctx = NormCtx {
        fuel: DEFAULT_NORMALIZE_FUEL,
        complete: true,
    };
    let nf = normalize_nf(tc, expr, &mut ctx);
    flat_digest(&canonicalize_comm(&nf))
}

/// The **environment-free** rewrite-canonical digest: canonical commutative-operand
/// ordering applied to `expr` *as given* (no kernel `whnf` normalisation, so no
/// `TypeChecker`/env is needed), then hash. This is the corpus-wide-computable Tier-1.5
/// key — it collapses commutative reorderings (`a + b` / `b + a`, `P ∧ Q` / `Q ∧ P`) on a
/// statement reconstructed straight from a `.mathverse` shard, with no env to normalise
/// against. Strictly weaker than [`rewrite_canonical_digest`] (it skips defeq), but a sound
/// *bucketing* key over the whole corpus; `same_object` remains the arbiter for a hit.
#[must_use]
pub fn structural_rewrite_digest(expr: &Expr) -> String {
    flat_digest(&canonicalize_comm(expr))
}

/// Known commutative operators paired with the **total spine arity** at which their two
/// explicit operands ARE the last two application arguments. In elaborated kernel terms
/// implicit/instance arguments are always present, so these arities are exact:
/// `@HAdd.hAdd {α β γ} [inst] a b` is always 6 args, `@Eq {α} a b` always 3, `And a b`
/// always 2. We reorder the last two operands only when the spine length equals this
/// arity; a partial (or over-) application — whose last two args are NOT both operands
/// (e.g. `@Eq α a`, the section `a = ·`) — is left untouched. That is a conservative
/// non-collapse (a search MISS), never a false merge of two genuinely distinct objects.
///
/// This is a Tier-1.5 *bucketing* heuristic, never a soundness claim. Extensible; the
/// curated core covers the common arithmetic/logical operators. Bare `max`/`min` are
/// intentionally absent (their elaborated arity is ambiguous across instances — `Nat.max`
/// vs `@max {α} [inst]`; `Max.max`/`Min.min` carry the canonical reorder instead).
const COMMUTATIVE_OPS: &[(&str, usize)] = &[
    ("HAdd.hAdd", 6), // @HAdd.hAdd {α β γ} [inst] a b
    ("HMul.hMul", 6),
    ("Add.add", 4), // @Add.add {α} [inst] a b
    ("Mul.mul", 4),
    ("Max.max", 4),
    ("Min.min", 4),
    ("Nat.add", 2), // Nat.add a b (no implicits)
    ("Int.add", 2),
    ("Nat.mul", 2),
    ("Int.mul", 2),
    ("And", 2), // And a b
    ("Or", 2),
    ("Iff", 2),
    ("Eq", 3), // @Eq {α} a b
];

/// The full-application spine arity of `name` if it is a known commutative operator.
///
/// Compares against the 14 [`COMMUTATIVE_OPS`] entries pre-interned as `Name`s
/// once, via `Name` equality (cached-hash fast path), instead of allocating a
/// fresh dotted-name `String` per call — this runs for every `App`-spine head of
/// every graduated statement (corpus-scale `structural_rewrite_digest`). The
/// returned arity is identical for identical names, so every digest is unchanged.
fn commutative_full_arity(name: &Name) -> Option<usize> {
    static OPS: std::sync::LazyLock<Vec<(Name, usize)>> = std::sync::LazyLock::new(|| {
        COMMUTATIVE_OPS
            .iter()
            .map(|(n, arity)| (Name::from_string(n), *arity))
            .collect()
    });
    OPS.iter().find(|(n, _)| n == name).map(|(_, arity)| *arity)
}

/// Flatten an application spine `f a1 a2 … an` into `(f, [a1, …, an])`.
fn spine(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args: Vec<&Expr> = Vec::new();
    let mut cur = e;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

/// Combine a node tag with child digests into a structural Merkle digest (O(1) per node).
fn merkle(tag: u8, parts: &[&[u8]]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(&[tag]);
    for p in parts {
        h.update(p);
    }
    *h.finalize().as_bytes()
}

/// Like [`merkle`] but streams `name`'s `Display` bytes (right after the tag,
/// matching the old `name.to_string().as_bytes()` placement) directly into the
/// hasher, then the trailing `parts` — avoiding a `String` allocation per
/// `Const`/`Let`/`Proj` node on the corpus-scale canon pass. The hashed byte
/// sequence is byte-identical to `merkle(tag, &[name.to_string().as_bytes(), ..])`,
/// so the Merkle key (an internal ordering key only) is unchanged.
fn merkle_with_name(tag: u8, name: &Name, parts: &[&[u8]]) -> [u8; 32] {
    use std::fmt::Write;
    struct HashWrite<'a>(&'a mut blake3::Hasher);
    impl std::fmt::Write for HashWrite<'_> {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            self.0.update(s.as_bytes());
            Ok(())
        }
    }
    let mut h = blake3::Hasher::new();
    h.update(&[tag]);
    // Display is the single source of the bytes `to_string()` would produce.
    let _ = write!(HashWrite(&mut h), "{name}");
    for p in parts {
        h.update(p);
    }
    *h.finalize().as_bytes()
}

/// Bottom-up canonicalisation returning `(canonical expr, structural Merkle digest)`.
///
/// The digest is an **internal ordering key only** — it decides which way to reorder a
/// commutative operator's two operands. Crucially it is computed by combining child digests
/// in O(1) per node, so the whole pass is **O(term size)**. (The previous implementation
/// re-`flat_digest`-ed each operand *subtree* from scratch to order it, which is quadratic
/// on equation-heavy corpora — every `lhs = rhs` re-encoded both sides at the root `Eq`.)
/// The public Tier-1.5 digest is still `flat_digest` of the returned canonical expr, so a
/// Merkle collision (≈2⁻¹²⁸) at worst skips one reorder (a search MISS), never a false merge.
fn canon(e: &Expr) -> (Expr, [u8; 32]) {
    match e.kind() {
        ExprKind::App(..) => {
            let (head, args) = spine(e);
            let (chead, hd) = canon(head);
            let mut cargs: Vec<(Expr, [u8; 32])> = args.iter().map(|a| canon(a)).collect();
            if let ExprKind::Const(name, _) = chead.kind() {
                if let Some(arity) = commutative_full_arity(name) {
                    // Only a full application places both operands in the last two args.
                    if cargs.len() == arity {
                        let n = cargs.len();
                        if cargs[n - 2].1 > cargs[n - 1].1 {
                            cargs.swap(n - 2, n - 1);
                        }
                    }
                }
            }
            let mut h = blake3::Hasher::new();
            h.update(b"A");
            h.update(&hd);
            let mut out = chead;
            for (a, d) in cargs {
                h.update(&d);
                out = Expr::app(out, a);
            }
            (out, *h.finalize().as_bytes())
        }
        ExprKind::Lam(bd, ty, body) => {
            let (cty, dt) = canon(ty);
            let (cb, db) = canon(body);
            (Expr::lam(*bd, cty, cb), merkle(b'L', &[&dt, &db]))
        }
        ExprKind::Pi(bd, ty, body) => {
            let (cty, dt) = canon(ty);
            let (cb, db) = canon(body);
            (Expr::pi(*bd, cty, cb), merkle(b'P', &[&dt, &db]))
        }
        ExprKind::Let(name, ty, val, body, nd) => {
            let (cty, dt) = canon(ty);
            let (cv, dv) = canon(val);
            let (cb, db) = canon(body);
            (
                Expr::let_named(name.clone(), cty, cv, cb, *nd),
                merkle_with_name(b'E', name, &[&dt, &dv, &db]),
            )
        }
        ExprKind::Proj(name, idx, s) => {
            let (cs, ds) = canon(s);
            (
                Expr::proj(name.clone(), *idx, cs),
                merkle_with_name(b'J', name, &[&(*idx as u64).to_le_bytes(), &ds]),
            )
        }
        ExprKind::MData(_, inner) => canon(inner),
        // Hot leaves get a cheap structural key (no per-leaf flat-encode); everything else
        // (Sort/FVar/Lit/SProp + the non-core Squash/Cubical*/ZFC* modes) falls back to the
        // exact flat digest, computed once per occurrence.
        ExprKind::Const(name, _) => (e.clone(), merkle_with_name(b'C', name, &[])),
        ExprKind::BVar(i) => (e.clone(), merkle(b'B', &[&(*i as u64).to_le_bytes()])),
        _ => (e.clone(), flat_raw(e)),
    }
}

/// Tier-1.5 canonicalisation: reorder the last two operands of every FULLY-APPLIED
/// commutative-operator spine (see [`COMMUTATIVE_OPS`]) into a canonical key order.
/// Deterministic, terminating (post-order over a finite term), and confluent. Partial
/// applications are left as-is. O(term size) — see [`canon`].
fn canonicalize_comm(e: &Expr) -> Expr {
    canon(e).0
}

/// The **sound** sameness decision: are `a` and `b` definitionally equal (the same
/// object)? Run to confirm a digest-bucket match. Delegates to the kernel.
#[must_use]
pub(crate) fn same_object(tc: &TypeChecker, a: &Expr, b: &Expr) -> bool {
    tc.is_def_eq(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::expr::BinderData;
    use clean_kernel::{Environment, Level};

    fn tc(env: &Environment) -> TypeChecker<'_> {
        TypeChecker::new(env)
    }

    // Prop sort, a convenient closed atomic type for building test terms.
    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    #[test]
    fn test_beta_redex_normalizes_to_argument() {
        let env = Environment::default();
        let tc = tc(&env);
        // (λ x : Prop, x) Prop   ↝β   Prop
        let id = Expr::lam(BinderData::default(), prop(), Expr::bvar(0));
        let redex = Expr::app(id, prop());

        let red_id = defeq_canonical_digest(&tc, &redex);
        let nf_id = defeq_canonical_digest(&tc, &prop());

        // The redex and its reduct share a canonical (defeq) digest …
        assert_eq!(red_id.canonical_digest, nf_id.canonical_digest);
        // … but NOT a structural one (different forms — the whole point).
        assert_ne!(red_id.structural_digest, nf_id.structural_digest);
        assert!(red_id.complete && nf_id.complete);
    }

    #[test]
    fn test_same_object_is_sound_defeq() {
        let env = Environment::default();
        let tc = tc(&env);
        let id = Expr::lam(BinderData::default(), prop(), Expr::bvar(0));
        let redex = Expr::app(id, prop());
        // is_def_eq confirms the beta pair are the same object …
        assert!(same_object(&tc, &redex, &prop()));
        // … and distinguishes genuinely different objects.
        let other = Expr::sort(Level::succ(Level::zero())); // Type 0 ≠ Prop
        assert!(!same_object(&tc, &prop(), &other));
    }

    #[test]
    fn test_distinct_objects_get_distinct_digests() {
        let env = Environment::default();
        let tc = tc(&env);
        let a = defeq_canonical_digest(&tc, &prop());
        let b = defeq_canonical_digest(&tc, &Expr::sort(Level::succ(Level::zero())));
        assert_ne!(a.canonical_digest, b.canonical_digest);
    }

    // `op a b` as a curried application spine.
    fn bin(op: &str, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(Expr::const_str(op), x), y)
    }

    #[test]
    fn test_tier15_collapses_commutative_operands() {
        let env = Environment::default();
        let tc = tc(&env);
        let p = Expr::const_str("P");
        let q = Expr::const_str("Q");
        // `P ∧ Q` and `Q ∧ P` are NOT defeq (different structure) …
        let pq = bin("And", p.clone(), q.clone());
        let qp = bin("And", q.clone(), p.clone());
        let id_pq = defeq_canonical_digest(&tc, &pq);
        let id_qp = defeq_canonical_digest(&tc, &qp);
        assert_ne!(
            id_pq.canonical_digest, id_qp.canonical_digest,
            "And is not defeq-commutative"
        );
        // … but Tier-1.5 buckets them together (commutative-operand canonicalisation).
        assert_eq!(
            id_pq.rewrite_digest, id_qp.rewrite_digest,
            "Tier-1.5 should collapse P∧Q and Q∧P"
        );
        assert_eq!(
            rewrite_canonical_digest(&tc, &pq),
            rewrite_canonical_digest(&tc, &qp)
        );
    }

    #[test]
    fn test_tier15_preserves_noncommutative_operands() {
        let env = Environment::default();
        let tc = tc(&env);
        let p = Expr::const_str("P");
        let q = Expr::const_str("Q");
        // `f P Q` vs `f Q P` for a NON-commutative `f`: must stay distinct (no spurious
        // collapse — order is meaning here).
        let fpq = bin("SomePkg.notComm", p.clone(), q.clone());
        let fqp = bin("SomePkg.notComm", q, p);
        assert_ne!(
            rewrite_canonical_digest(&tc, &fpq),
            rewrite_canonical_digest(&tc, &fqp)
        );
    }

    #[test]
    fn test_structural_rewrite_digest_is_env_free_and_collapses_commutative() {
        // The corpus-wide key needs NO TypeChecker/env. It still collapses commutative
        // reorderings (the whole point: "same object, different form" at corpus scale).
        let p = Expr::const_str("P");
        let q = Expr::const_str("Q");
        let pq = bin("And", p.clone(), q.clone());
        let qp = bin("And", q.clone(), p.clone());
        assert_eq!(
            structural_rewrite_digest(&pq),
            structural_rewrite_digest(&qp),
            "env-free Tier-1.5 must bucket P∧Q with Q∧P"
        );
        // … and a NON-commutative head keeps operand order meaningful (no spurious collapse).
        let fpq = bin("SomePkg.notComm", p.clone(), q.clone());
        let fqp = bin("SomePkg.notComm", q, p);
        assert_ne!(
            structural_rewrite_digest(&fpq),
            structural_rewrite_digest(&fqp)
        );
        // For a term with no commutative operator, the env-free digest equals the plain
        // structural digest (canonicalize_comm is identity), so corpus types reconstructed
        // from a shard key identically whether or not they contain commutative ops.
        let env = Environment::default();
        let tc = tc(&env);
        let plain = Expr::sort(Level::zero());
        assert_eq!(
            structural_rewrite_digest(&plain),
            defeq_canonical_digest(&tc, &plain).structural_digest
        );
    }

    #[test]
    fn test_partial_application_of_commutative_op_is_not_collapsed() {
        // `@Eq α a` (a partial application — the section `a = ·`) has only TWO spine args,
        // but `Eq`'s operands are its LAST TWO at full arity 3 (`@Eq α a b`). The arity guard
        // must NOT swap `α`/`a` here: a type argument is not an operand. So `@Eq α a` and the
        // distinct `@Eq a α` must keep DIFFERENT digests (a conservative non-collapse), where
        // a naive "swap the last two spine args" would have falsely merged them.
        let alpha = Expr::const_str("MyType");
        let a = Expr::const_str("a");
        let eq_alpha_a = bin("Eq", alpha.clone(), a.clone()); // @Eq MyType a  (partial)
        let eq_a_alpha = bin("Eq", a, alpha); // @Eq a MyType  (partial, type/operand swapped)
        assert_ne!(
            structural_rewrite_digest(&eq_alpha_a),
            structural_rewrite_digest(&eq_a_alpha),
            "partial application of Eq (arity 3) must not reorder its 2-arg spine"
        );

        // The FULLY-applied form `@Eq α a b` (3 args) still collapses its two operands a,b.
        let full_ab = Expr::app(
            bin("Eq", Expr::const_str("T"), Expr::const_str("x")),
            Expr::const_str("y"),
        );
        let full_ba = Expr::app(
            bin("Eq", Expr::const_str("T"), Expr::const_str("y")),
            Expr::const_str("x"),
        );
        assert_eq!(
            structural_rewrite_digest(&full_ab),
            structural_rewrite_digest(&full_ba),
            "fully-applied @Eq T x y and @Eq T y x must collapse (operands are the last two)"
        );
    }
}
