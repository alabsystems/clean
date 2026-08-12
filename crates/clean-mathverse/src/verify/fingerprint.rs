// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Content fingerprint for declarations — the stable cache key behind
//! re-import deduplication (see
//! `designs/2026-06-27-reimport-at-the-speed-of-a-hash.md`, move P1).
//!
//! ## Why a content fingerprint
//!
//! The kernel verdict on a declaration — does `value : type` type-check, and
//! what is its transitive axiom closure — is a *deterministic function of the
//! declaration's kernel-relevant content*: its kind, universe parameters, type,
//! and (where present) value. It does **not** depend on the declaration's own
//! name: the name is a label, and `value : type` is checked identically
//! whatever the declaration is called. So two declarations with byte-identical
//! content share a verdict, and we want them to share a fingerprint — verify the
//! content once, reuse the verdict. On re-import of an unchanged library that
//! turns an O(library) re-verify into O(changed decls).
//!
//! ## Why this is a *sound* cache key
//!
//! - **Canonical.** The `Expr` tree contains no `HashMap`
//!   (`MDataMap = Vec<(Name, _)>`, `LevelVec = SmallVec`, every container is
//!   ordered), and `impl Serialize for Expr` emits only the structural
//!   `ExprKind` (the cached `ExprMeta` is recomputed on deserialize, never
//!   serialized). So serialization is order-deterministic and
//!   metadata-independent.
//! - **Alpha-canonical.** `Expr` uses de Bruijn indices, so syntactic
//!   (serialized) equality is alpha-equality: alpha-equivalent terms fingerprint
//!   identically.
//! - **Portable & collision-free.** `bincode` fixes a length-prefixed,
//!   fixed-endian binary encoding and `blake3` a 256-bit digest, so the
//!   fingerprint is stable across runs and machines with a second-preimage
//!   margin far beyond library scale.
//!
//! ## Soundness boundary
//!
//! A fingerprint is **only a cache key**. It never decides a verdict; it only
//! decides whether a verdict already computed for byte-identical content may be
//! reused. The TCB is unchanged — the cache memoizes the pure, deterministic
//! kernel verdict. A sampling ratchet (future work, P1) re-checks cached entries
//! from a cold kernel to prove `cache ≡ fresh`, and any skeptic can discard the
//! cache and re-derive every fingerprint bit-for-bit.

use clean_kernel::expr::Expr;
use clean_kernel::{Declaration, Name};

/// Errors from computing a [`decl_content_fingerprint`].
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum FingerprintError {
    /// The declaration's content could not be encoded to canonical bytes. In
    /// practice unreachable for well-formed kernel declarations (the `Expr`
    /// tree is composed entirely of length-known, serde-encodable containers),
    /// but surfaced as a typed error rather than a panic to keep the path
    /// `unwrap`-free.
    #[error("declaration content encode failed: {0}")]
    Encode(#[from] bincode::error::EncodeError),
}

/// Tag distinguishing the four declaration kinds. Part of the fingerprint so a
/// `Theorem` and a `Definition` with identical type/value never collide: they
/// take different kernel intake paths (`add_theorem` vs `add_definition`) and
/// are therefore distinct verification work with potentially distinct verdicts.
fn kind_tag(decl: &Declaration) -> u8 {
    match decl {
        Declaration::Definition { .. } => 0,
        Declaration::Theorem { .. } => 1,
        Declaration::Opaque { .. } => 2,
        Declaration::Axiom { .. } => 3,
    }
}

/// The `(level_params, type, optional value)` that determine the kernel verdict.
/// The declaration's own `name` and the `is_reducible` hint are excluded:
/// neither affects whether `value : type` type-checks.
fn content_parts(decl: &Declaration) -> (&[Name], &Expr, Option<&Expr>) {
    match decl {
        Declaration::Definition {
            level_params,
            type_,
            value,
            ..
        } => (level_params, type_, Some(value)),
        Declaration::Theorem {
            level_params,
            type_,
            value,
            ..
        } => (level_params, type_, Some(value)),
        Declaration::Opaque {
            level_params,
            type_,
            value,
            ..
        } => (level_params, type_, Some(value)),
        Declaration::Axiom {
            level_params,
            type_,
            ..
        } => (level_params, type_, None),
    }
}

/// Stable 32-byte content fingerprint of a declaration's kernel-relevant content
/// (kind ⊕ universe params ⊕ type ⊕ value). The cache key behind re-import
/// dedup; see the module docs for the soundness boundary.
pub(crate) fn decl_content_fingerprint(decl: &Declaration) -> Result<[u8; 32], FingerprintError> {
    let (level_params, type_, value) = content_parts(decl);
    // Canonical content tuple: discriminant first so kinds never alias, then the
    // verdict-determining payload. Encoded with bincode's fixed, deterministic
    // format and digested with blake3 (256-bit).
    let content = (kind_tag(decl), level_params, type_, value);
    let bytes = bincode::serde::encode_to_vec(content, bincode::config::standard())?;
    Ok(*blake3::hash(&bytes).as_bytes())
}

/// The declaration's own fully-qualified name.
#[cfg(test)]
fn decl_name(decl: &Declaration) -> &Name {
    match decl {
        Declaration::Definition { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. }
        | Declaration::Axiom { name, .. } => name,
    }
}

/// The constants directly referenced by a declaration's type and value — its
/// `direct_deps` for the Merkle-DAG verified hash. The declaration's own name is
/// excluded (a constant is not its own dependency).
#[cfg(test)]
pub(crate) fn direct_dep_names(decl: &Declaration) -> std::collections::HashSet<Name> {
    let (_, type_, value) = content_parts(decl);
    let mut set = type_.collect_constants();
    if let Some(v) = value {
        v.collect_constants_into(&mut set);
    }
    set.remove(decl_name(decl));
    set
}

/// Merkle-DAG **verified hash** of a declaration: the cross-version-sound cache
/// key.
///
/// `vh(d) = blake3(leaf_fp(d) ‖ sorted[ dep_hash(dep) for dep ∈ direct_deps(d) ])`
///
/// The leaf fingerprint ([`decl_content_fingerprint`]) captures `d`'s own
/// structure including the *names* it references; folding in each dependency's
/// hash additionally captures the dependencies' *content*. So if a dependency's
/// body or type changes under a fixed name, `dep_hash(dep)` changes, `vh(d)`
/// changes, and every transitive dependent misses the cache and is re-checked —
/// the property a name-keyed cache lacks.
///
/// `dep_hash` resolves a dependency name to its hash: the `vh` of an
/// already-processed declaration, or the leaf fingerprint of a trusted-closure
/// constant. Returns `Ok(None)` when *any* dependency is unresolved — the caller
/// then cannot soundly reuse a cached verdict and must verify `d` fresh.
#[cfg(test)]
pub(crate) fn decl_verified_hash(
    decl: &Declaration,
    dep_hash: impl Fn(&Name) -> Option<[u8; 32]>,
) -> Result<Option<[u8; 32]>, FingerprintError> {
    let leaf = decl_content_fingerprint(decl)?;
    let mut dep_hashes: Vec<[u8; 32]> = Vec::new();
    for dep in direct_dep_names(decl) {
        match dep_hash(&dep) {
            Some(h) => dep_hashes.push(h),
            // An unresolved dependency means we cannot form a sound verified
            // hash — signal a forced cache miss rather than hashing a hole.
            None => return Ok(None),
        }
    }
    // Sort the resolved dependency hashes so `vh` is independent of the
    // set-iteration order of `direct_dep_names`.
    dep_hashes.sort_unstable();
    let mut hasher = blake3::Hasher::new();
    hasher.update(&leaf);
    for h in &dep_hashes {
        hasher.update(h);
    }
    Ok(Some(*hasher.finalize().as_bytes()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::expr::ExprKind;
    use std::collections::HashMap;
    use std::sync::Arc;

    /// A `Const` expression with no universe arguments — a convenient distinct
    /// leaf for building test declarations without needing a `Level`.
    fn c(s: &str) -> Expr {
        Expr::from_kind(ExprKind::Const(Name::from_string(s), Default::default()))
    }

    /// `f a` — a small non-leaf expression, to exercise the `Arc<Expr>` path.
    fn app(f: Expr, a: Expr) -> Expr {
        Expr::from_kind(ExprKind::App(Arc::new(f), Arc::new(a)))
    }

    fn thm(name: &str, type_: Expr, value: Expr) -> Declaration {
        Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        }
    }

    fn def(name: &str, type_: Expr, value: Expr) -> Declaration {
        Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
            is_reducible: false,
        }
    }

    fn fp(decl: &Declaration) -> [u8; 32] {
        decl_content_fingerprint(decl).expect("well-formed decl fingerprints")
    }

    #[test]
    fn test_fingerprint_deterministic_across_independent_construction() {
        // Two independently-built but structurally-identical declarations must
        // produce the same fingerprint — the property the cache relies on.
        let a = thm("Foo.bar", app(c("Eq"), c("p")), c("proof"));
        let b = thm("Foo.bar", app(c("Eq"), c("p")), c("proof"));
        assert_eq!(fp(&a), fp(&b), "identical content must fingerprint equally");
    }

    #[test]
    fn test_fingerprint_independent_of_declaration_name() {
        // The verdict `value : type` does not depend on the label, so neither
        // does the fingerprint — this is what lets a renamed-but-identical proof
        // reuse a cached verdict.
        let a = thm("Foo.bar", c("T"), c("proof"));
        let b = thm("Completely.Different.Name", c("T"), c("proof"));
        assert_eq!(fp(&a), fp(&b), "name must not affect the fingerprint");
    }

    #[test]
    fn test_fingerprint_sensitive_to_type() {
        let a = thm("x", c("TypeA"), c("proof"));
        let b = thm("x", c("TypeB"), c("proof"));
        assert_ne!(
            fp(&a),
            fp(&b),
            "differing type must fingerprint differently"
        );
    }

    #[test]
    fn test_fingerprint_sensitive_to_value() {
        let a = thm("x", c("T"), c("proofA"));
        let b = thm("x", c("T"), c("proofB"));
        assert_ne!(
            fp(&a),
            fp(&b),
            "differing value must fingerprint differently"
        );
    }

    #[test]
    fn test_fingerprint_sensitive_to_kind() {
        // A theorem and a definition with identical type/value are distinct
        // verification work (different intake paths) and must not alias.
        let t = thm("x", c("T"), c("v"));
        let d = def("x", c("T"), c("v"));
        assert_ne!(fp(&t), fp(&d), "kind must affect the fingerprint");
    }

    #[test]
    fn test_fingerprint_axiom_has_no_value_and_is_distinct() {
        // An axiom (no value) over type T must fingerprint, and must differ from
        // a theorem over the same type.
        let ax = Declaration::Axiom {
            name: Name::from_string("x"),
            level_params: vec![],
            type_: c("T"),
        };
        let t = thm("x", c("T"), c("v"));
        let _ = fp(&ax);
        assert_ne!(fp(&ax), fp(&t), "axiom and theorem must not alias");
    }

    /// Build a name→hash resolver from `(name, byte)` pairs (each byte fills the
    /// 32-byte hash). Unlisted names resolve to `None`.
    fn resolver(pairs: &[(&str, u8)]) -> HashMap<Name, [u8; 32]> {
        pairs
            .iter()
            .map(|(n, b)| (Name::from_string(n), [*b; 32]))
            .collect()
    }

    #[test]
    fn test_vh_is_deterministic() {
        // Theorem `T : Prop := DepA DepB` — references {Prop, DepA, DepB}.
        let d = thm("T", c("Prop"), app(c("DepA"), c("DepB")));
        let r = resolver(&[("Prop", 1), ("DepA", 2), ("DepB", 3)]);
        let a = decl_verified_hash(&d, |n| r.get(n).copied()).expect("ok");
        let b = decl_verified_hash(&d, |n| r.get(n).copied()).expect("ok");
        assert_eq!(a, b, "vh must be deterministic");
        assert!(a.is_some(), "all deps resolved");
    }

    #[test]
    fn test_vh_changes_when_a_dependency_hash_changes() {
        // THE cross-version-soundness property: same decl, but a dependency's
        // content (hash) changed → the verified hash must change so the
        // dependent misses the cache and is re-checked.
        let d = thm("T", c("Prop"), app(c("DepA"), c("DepB")));
        let r1 = resolver(&[("Prop", 1), ("DepA", 2), ("DepB", 3)]);
        let r2 = resolver(&[("Prop", 1), ("DepA", 99), ("DepB", 3)]); // DepA changed
        let v1 = decl_verified_hash(&d, |n| r1.get(n).copied()).expect("ok");
        let v2 = decl_verified_hash(&d, |n| r2.get(n).copied()).expect("ok");
        assert_ne!(v1, v2, "a changed dependency must change vh");
    }

    #[test]
    fn test_vh_none_when_a_dependency_is_unresolved() {
        // An unresolved dependency means no sound vh — forced cache miss.
        let d = thm("T", c("Prop"), c("MissingDep"));
        let r = resolver(&[("Prop", 1)]); // MissingDep absent
        let v = decl_verified_hash(&d, |n| r.get(n).copied()).expect("ok");
        assert!(v.is_none(), "unresolved dep ⇒ vh is None (forced re-check)");
    }

    #[test]
    fn test_vh_excludes_self_reference() {
        // A declaration is not its own dependency: even if its value mentions its
        // own name, the resolver need not know that name.
        let d = thm("Foo", c("Prop"), app(c("Foo"), c("Bar")));
        let r = resolver(&[("Prop", 1), ("Bar", 2)]); // "Foo" intentionally absent
        let v = decl_verified_hash(&d, |n| r.get(n).copied()).expect("ok");
        assert!(
            v.is_some(),
            "self-reference must not be a required dependency"
        );
    }
}
