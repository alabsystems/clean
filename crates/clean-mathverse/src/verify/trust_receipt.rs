// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Merkle **trust receipt** over a kernel-verified declaration set
//! (`designs/2026-06-27-reimport-at-the-speed-of-a-hash.md`, move **P4**).
//!
//! # What it is
//!
//! A single 32-byte root hash committing to *every* declaration Clean's kernel
//! accepted in a stamp run, plus the union of their axiom closures. Published as:
//!
//! > `Mathlib@<sha> → Clean root <32 bytes>, axioms ⊆ {propext, Quot.sound,
//! > Classical.choice}, N decls, independently re-derivable.`
//!
//! Anyone can then either (a) prove one theorem's membership with an O(log N)
//! Merkle path, or (b) re-derive the whole root from the published leaves and
//! audit it against a fresh kernel run. No one in the Lean ecosystem has a single
//! hash certifying an entire library type-checks under a named axiom basis.
//!
//! # Why it is sound (and why it is NOT the abandoned verdict-*skip*)
//!
//! This is a hash *over verdicts the kernel already produced* — it never lets a
//! declaration be accepted without a real `check_type`. It is the **sound
//! replacement** for the struck P1 verdict-skip (which was both wrong-bottleneck
//! and forgeable-cross-run as a stamp backing): the receipt does not *replace*
//! verification, it *commits to* it. The TCB is unchanged; a skeptic recomputes
//! the root from scratch. `blake3` is collision-resistant, so the root binds the
//! exact `{(name, content-hash)}` set — you cannot exhibit a different verified
//! set under the same root.
//!
//! # Canonical construction (must be byte-identical across independent builders)
//!
//! * **Leaf** for `(name, content_hash)`:
//!   `H(0x00 ‖ name_utf8 ‖ 0x1f ‖ content_hash)`. Binding the name makes a
//!   membership proof a statement about a *named* theorem; binding the content
//!   hash makes it a statement about that theorem's *verified content*.
//! * **Internal node**: `H(0x01 ‖ left ‖ right)`.
//! * **Odd node at a level**: promoted UNCHANGED to the next level (no
//!   duplication — avoids the duplicate-leaf second-preimage ambiguity).
//! * **Empty set**: a fixed domain-separated constant [`EMPTY_ROOT`].
//! * Leaves are sorted by `(name, content_hash)` before building, so the root is
//!   independent of input order and duplicate `(name, content_hash)` pairs are
//!   de-duplicated (a set commitment, not a multiset).

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

/// Domain-separation tags. Any change here is a breaking root-recipe change and
/// must bump [`TrustReceipt::SCHEMA_VERSION`].
const TAG_LEAF: u8 = 0x00;
const TAG_NODE: u8 = 0x01;
const TAG_EMPTY: &[u8] = b"clean-trust-receipt/v1/empty";
/// Separator between the name and the content hash inside a leaf preimage (US,
/// "unit separator" — never appears in a Lean name).
const LEAF_SEP: u8 = 0x1f;

/// The three Lean foundational axioms — the trust basis a `KernelVerified`
/// Mathlib is expected to rest on. A receipt whose axiom closure is a subset of
/// this set is `within_tcb`.
pub const TCB_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"];

/// Root of the empty verified set (no leaves) — a defined constant so an empty
/// receipt is still a well-formed, verifiable commitment.
#[must_use]
pub fn empty_root() -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(TAG_EMPTY);
    *h.finalize().as_bytes()
}

/// Hash one `(name, content_hash)` pair into its Merkle leaf.
#[must_use]
pub fn leaf_hash(name: &str, content_hash: &[u8; 32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(&[TAG_LEAF]);
    h.update(name.as_bytes());
    h.update(&[LEAF_SEP]);
    h.update(content_hash);
    *h.finalize().as_bytes()
}

/// Hash two child hashes into their parent node.
fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(&[TAG_NODE]);
    h.update(left);
    h.update(right);
    *h.finalize().as_bytes()
}

/// Canonicalize `named_leaves` into the SORTED, DEDUPED leaf-hash vector the tree
/// is built over. Sorting by `(name, content_hash)` makes the root
/// order-independent; the `BTreeSet` de-dupes exact repeats so the commitment is
/// to a set. Returns the canonical `(name, content_hash)` order alongside, so a
/// caller can map a name to its leaf index for a membership proof.
#[must_use]
pub fn canonical_leaves(
    named_leaves: &[(String, [u8; 32])],
) -> (Vec<(String, [u8; 32])>, Vec<[u8; 32]>) {
    let set: BTreeSet<(String, [u8; 32])> = named_leaves.iter().cloned().collect();
    let ordered: Vec<(String, [u8; 32])> = set.into_iter().collect();
    let hashes: Vec<[u8; 32]> = ordered.iter().map(|(n, ch)| leaf_hash(n, ch)).collect();
    (ordered, hashes)
}

/// Compute the Merkle root of already-canonical `leaf_hashes` (sorted+deduped by
/// [`canonical_leaves`]). Empty input → [`empty_root`].
#[must_use]
pub fn merkle_root(leaf_hashes: &[[u8; 32]]) -> [u8; 32] {
    if leaf_hashes.is_empty() {
        return empty_root();
    }
    let mut level: Vec<[u8; 32]> = leaf_hashes.to_vec();
    while level.len() > 1 {
        let mut next: Vec<[u8; 32]> = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            next.push(node_hash(&level[i], &level[i + 1]));
            i += 2;
        }
        if i < level.len() {
            // Odd node: promote unchanged to the next level.
            next.push(level[i]);
        }
        level = next;
    }
    level[0]
}

/// One step of a membership path: the sibling hash and whether the sibling sits
/// on the LEFT of the node being folded up (so the verifier orders the concat
/// correctly). A promoted odd node contributes no step (it simply rises).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleStep {
    /// The sibling hash to combine with the running hash.
    #[serde(with = "hex32")]
    pub sibling: [u8; 32],
    /// `true` if `sibling` is the LEFT child (running hash is the right child).
    pub sibling_is_left: bool,
}

/// An O(log N) proof that a leaf is a member of the tree with a given root.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleProof {
    /// Steps from leaf up to the root.
    pub path: Vec<MerkleStep>,
}

/// Build a membership proof for the leaf at canonical index `index` over
/// already-canonical `leaf_hashes`. Returns `None` if `index` is out of range.
#[must_use]
pub fn merkle_proof(leaf_hashes: &[[u8; 32]], index: usize) -> Option<MerkleProof> {
    if index >= leaf_hashes.len() {
        return None;
    }
    let mut path = Vec::new();
    let mut level: Vec<[u8; 32]> = leaf_hashes.to_vec();
    let mut idx = index;
    while level.len() > 1 {
        let mut next: Vec<[u8; 32]> = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            if i == idx {
                // Our node is the LEFT child; sibling is the right one.
                path.push(MerkleStep {
                    sibling: level[i + 1],
                    sibling_is_left: false,
                });
            } else if i + 1 == idx {
                // Our node is the RIGHT child; sibling is the left one.
                path.push(MerkleStep {
                    sibling: level[i],
                    sibling_is_left: true,
                });
            }
            next.push(node_hash(&level[i], &level[i + 1]));
            i += 2;
        }
        if i < level.len() {
            // A lone odd node at the end. If it is ours, it is promoted with no
            // sibling step; otherwise it does not touch our path.
            next.push(level[i]);
        }
        idx /= 2;
        level = next;
    }
    Some(MerkleProof { path })
}

/// Verify that `leaf` (already the [`leaf_hash`] of a `(name, content_hash)`) is
/// committed by `root` via `proof`. Recomputes the root from the leaf up and
/// compares. A single wrong/forged step yields a different root ⇒ `false`.
#[must_use]
pub fn verify_membership(root: &[u8; 32], leaf: &[u8; 32], proof: &MerkleProof) -> bool {
    let mut acc = *leaf;
    for step in &proof.path {
        acc = if step.sibling_is_left {
            node_hash(&step.sibling, &acc)
        } else {
            node_hash(&acc, &step.sibling)
        };
    }
    &acc == root
}

/// A published, independently re-derivable trust receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustReceipt {
    /// Recipe/format version — bump on any change to leaf/node tagging or the
    /// canonicalization, so a stale receipt is never mis-verified as current.
    pub schema_version: u32,
    /// What produced this receipt.
    pub generated_by: String,
    /// The Merkle root over the sorted, deduped `(name, content_hash)` leaves,
    /// hex-encoded.
    pub merkle_root: String,
    /// Number of distinct verified leaves under the root.
    pub leaf_count: usize,
    /// Sorted union of the verified set's axiom closure (the trust basis) — the
    /// genuine foundational axioms the verified decls transitively rest on. Only
    /// meaningful when `axiom_basis_complete` is `true`.
    pub axiom_closure: Vec<String>,
    /// Whether `axiom_closure` is the COMPLETE transitive axiom closure. A
    /// producer that cannot soundly compute it (e.g. the memory-elided
    /// per-constant path, whose types-only trusted loading hides the value DAG
    /// and mints value-less stubs indistinguishable from axioms) sets this
    /// `false` and leaves `axiom_closure` empty — the Merkle root over the
    /// verified leaves is still a sound commitment; only the axiom *claim* is
    /// deferred to a producer that walks the full value closure (the stamp path).
    pub axiom_basis_complete: bool,
    /// The TCB axiom basis this receipt is measured against.
    pub tcb_axioms: Vec<String>,
    /// `Some(axiom_closure ⊆ tcb_axioms)` — the headline trust claim — when
    /// `axiom_basis_complete`; `None` when the axiom basis was not computed.
    pub within_tcb: Option<bool>,
    /// Optional source identity being certified (e.g. `Mathlib@<git-sha>` or a
    /// toolchain/fingerprint string).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_id: Option<String>,
    /// Clean version that minted the receipt.
    pub clean_version: String,
}

impl TrustReceipt {
    /// Current receipt recipe version.
    pub const SCHEMA_VERSION: u32 = 1;

    /// Build a receipt over `named_leaves` (canonicalized internally) with the
    /// given `axiom_closure`. `within_tcb` is computed as `axiom_closure ⊆
    /// TCB_AXIOMS`. Returns the receipt plus the canonical `(name, content_hash)`
    /// order (needed to locate a name's leaf index for a membership proof).
    #[must_use]
    pub fn build(
        named_leaves: &[(String, [u8; 32])],
        axiom_closure: &[String],
        axiom_basis_complete: bool,
        source_id: Option<String>,
        clean_version: &str,
    ) -> (Self, Vec<(String, [u8; 32])>) {
        let (ordered, hashes) = canonical_leaves(named_leaves);
        let root = merkle_root(&hashes);
        // Only publish an axiom basis when the producer computed it soundly; a
        // partial/elided set must NOT masquerade as the trust basis.
        let axioms: Vec<String> = if axiom_basis_complete {
            axiom_closure
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        } else {
            Vec::new()
        };
        let tcb: BTreeSet<&str> = TCB_AXIOMS.iter().copied().collect();
        let within_tcb =
            axiom_basis_complete.then(|| axioms.iter().all(|a| tcb.contains(a.as_str())));
        let receipt = TrustReceipt {
            schema_version: Self::SCHEMA_VERSION,
            generated_by: "clean mathverse trust-receipt (P4)".to_string(),
            merkle_root: hexcodec::encode(&root),
            leaf_count: ordered.len(),
            axiom_closure: axioms,
            axiom_basis_complete,
            tcb_axioms: TCB_AXIOMS.iter().map(|s| s.to_string()).collect(),
            within_tcb,
            source_id,
            clean_version: clean_version.to_string(),
        };
        (receipt, ordered)
    }

    /// The declared root as raw bytes, if it is well-formed hex.
    #[must_use]
    pub fn root_bytes(&self) -> Option<[u8; 32]> {
        let v = hexcodec::decode(&self.merkle_root)?;
        v.try_into().ok()
    }

    /// **Audit**: independently re-derive the root from `named_leaves` and confirm
    /// it matches this receipt's declared root AND that the recomputed
    /// leaf/axiom counts and TCB verdict agree. This is the "any skeptic can
    /// re-derive it" property — it recomputes everything and trusts nothing in
    /// the receipt but its claims.
    #[must_use]
    pub fn verify_against_leaves(
        &self,
        named_leaves: &[(String, [u8; 32])],
        axiom_closure: &[String],
    ) -> bool {
        if self.schema_version != Self::SCHEMA_VERSION {
            return false;
        }
        let (recomputed, _) = Self::build(
            named_leaves,
            axiom_closure,
            self.axiom_basis_complete,
            self.source_id.clone(),
            &self.clean_version,
        );
        recomputed.merkle_root == self.merkle_root
            && recomputed.leaf_count == self.leaf_count
            && recomputed.axiom_closure == self.axiom_closure
            && recomputed.within_tcb == self.within_tcb
    }
}

/// One `(name, content_hash)` leaf, hex-serialized — the publishable, auditable
/// companion to a [`TrustReceipt`]. A verifier needs these to re-derive the root
/// and to build membership proofs; they are the decl-level detail the single
/// root hash commits to.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedLeaf {
    /// Fully-qualified declaration name.
    pub name: String,
    /// The declaration's name-independent content hash (hex).
    pub content_hash: String,
}

/// The full auditable leaf set behind a receipt: the source identity, the union
/// axiom closure, and every `(name, content_hash)` leaf. Published alongside the
/// receipt so anyone can re-derive the root and prove membership.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeavesManifest {
    /// Format version (matches the receipt recipe version it audits).
    pub schema_version: u32,
    /// What produced it.
    pub generated_by: String,
    /// Optional source identity (e.g. `Mathlib@<sha>`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_id: Option<String>,
    /// The non-foundational axiom closure of the verified set (empty ⇒ rests only
    /// on the foundational TCB, when `axiom_basis_complete`).
    pub axiom_closure: Vec<String>,
    /// Whether `axiom_closure` is the complete transitive closure — carried so a
    /// re-mint (`trust-receipt build`) reproduces the receipt's `within_tcb`
    /// verdict rather than guessing it from emptiness (an EMPTY closure is the
    /// clean, within-TCB case, not an unknown one).
    #[serde(default)]
    pub axiom_basis_complete: bool,
    /// The `(name, content_hash)` leaves (canonical order recommended but not
    /// required — [`Self::to_named_leaves`] re-canonicalizes).
    pub leaves: Vec<NamedLeaf>,
}

impl LeavesManifest {
    /// Build a manifest from raw `(name, content_hash)` pairs.
    #[must_use]
    pub fn new(
        named_leaves: &[(String, [u8; 32])],
        axiom_closure: &[String],
        axiom_basis_complete: bool,
        source_id: Option<String>,
    ) -> Self {
        let (ordered, _) = canonical_leaves(named_leaves);
        LeavesManifest {
            schema_version: TrustReceipt::SCHEMA_VERSION,
            generated_by: "clean mathverse trust-receipt (P4)".to_string(),
            source_id,
            axiom_basis_complete,
            axiom_closure: axiom_closure
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            leaves: ordered
                .into_iter()
                .map(|(name, ch)| NamedLeaf {
                    name,
                    content_hash: hexcodec::encode(&ch),
                })
                .collect(),
        }
    }

    /// Decode the leaves into `(name, [u8; 32])` pairs, or `None` if any
    /// `content_hash` is not 32-byte hex.
    #[must_use]
    pub fn to_named_leaves(&self) -> Option<Vec<(String, [u8; 32])>> {
        self.leaves
            .iter()
            .map(|l| {
                let bytes: [u8; 32] = hexcodec::decode(&l.content_hash)?.try_into().ok()?;
                Some((l.name.clone(), bytes))
            })
            .collect()
    }
}

/// Minimal, dependency-free hex codec (the workspace has no `hex` crate; the one
/// in `shard.rs` is a private module). Lowercase, fixed alphabet.
pub(crate) mod hexcodec {
    pub fn encode(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(bytes.len() * 2);
        for b in bytes {
            s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
            s.push(char::from_digit((b & 0x0f) as u32, 16).unwrap());
        }
        s
    }

    pub fn decode(s: &str) -> Option<Vec<u8>> {
        if !s.len().is_multiple_of(2) {
            return None;
        }
        let bytes = s.as_bytes();
        let mut out = Vec::with_capacity(s.len() / 2);
        let mut i = 0;
        while i < bytes.len() {
            let hi = (bytes[i] as char).to_digit(16)?;
            let lo = (bytes[i + 1] as char).to_digit(16)?;
            out.push(((hi << 4) | lo) as u8);
            i += 2;
        }
        Some(out)
    }
}

/// Serde codec for a `[u8; 32]` field rendered as lowercase hex.
mod hex32 {
    use super::hexcodec;
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hexcodec::encode(bytes))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
        let s = String::deserialize(d)?;
        let v = hexcodec::decode(&s).ok_or_else(|| serde::de::Error::custom("invalid hex"))?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 32-byte hex"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaves(spec: &[(&str, u8)]) -> Vec<(String, [u8; 32])> {
        spec.iter()
            .map(|(n, b)| (n.to_string(), [*b; 32]))
            .collect()
    }

    #[test]
    fn root_is_order_independent_and_dedups() {
        let a = leaves(&[("A", 1), ("B", 2), ("C", 3)]);
        let mut b = a.clone();
        b.reverse();
        b.push(("A".to_string(), [1u8; 32])); // duplicate
        let (_, ha) = canonical_leaves(&a);
        let (_, hb) = canonical_leaves(&b);
        assert_eq!(merkle_root(&ha), merkle_root(&hb), "root is set-committing");
    }

    #[test]
    fn any_leaf_change_changes_the_root() {
        let base = leaves(&[("A", 1), ("B", 2), ("C", 3)]);
        let (_, h0) = canonical_leaves(&base);
        let r0 = merkle_root(&h0);

        // Change one content hash.
        let mut changed = base.clone();
        changed[1].1 = [9u8; 32];
        let (_, h1) = canonical_leaves(&changed);
        assert_ne!(r0, merkle_root(&h1), "changed content ⇒ new root");

        // Add a leaf.
        let mut added = base.clone();
        added.push(("D".to_string(), [4u8; 32]));
        let (_, h2) = canonical_leaves(&added);
        assert_ne!(r0, merkle_root(&h2), "added decl ⇒ new root");

        // Remove a leaf.
        let removed = leaves(&[("A", 1), ("C", 3)]);
        let (_, h3) = canonical_leaves(&removed);
        assert_ne!(r0, merkle_root(&h3), "removed decl ⇒ new root");
    }

    #[test]
    fn empty_root_is_defined_and_distinct() {
        let (_, h) = canonical_leaves(&[]);
        assert_eq!(merkle_root(&h), empty_root());
        // The empty root differs from any single-leaf root.
        let (_, one) = canonical_leaves(&leaves(&[("A", 1)]));
        assert_ne!(merkle_root(&one), empty_root());
    }

    #[test]
    fn membership_proofs_verify_for_every_leaf_at_many_sizes() {
        // Exercise N = 1,2,3,...,17 (odd, even, powers of two) so the odd-node
        // promotion path is covered at multiple levels.
        for n in 1usize..=17 {
            let spec: Vec<(String, [u8; 32])> = (0..n)
                .map(|i| (format!("T{i:03}"), [(i as u8).wrapping_add(1); 32]))
                .collect();
            let (ordered, hashes) = canonical_leaves(&spec);
            let root = merkle_root(&hashes);
            for (idx, (name, ch)) in ordered.iter().enumerate() {
                let proof = merkle_proof(&hashes, idx).expect("in range");
                let leaf = leaf_hash(name, ch);
                assert!(
                    verify_membership(&root, &leaf, &proof),
                    "membership must verify for n={n} idx={idx}"
                );
                // A wrong leaf (different content) must NOT verify under the proof.
                let forged = leaf_hash(name, &[0xAB; 32]);
                assert!(
                    !verify_membership(&root, &forged, &proof),
                    "forged leaf must be rejected (n={n} idx={idx})"
                );
            }
        }
    }

    #[test]
    fn a_proof_from_a_different_tree_does_not_verify() {
        let (o1, h1) = canonical_leaves(&leaves(&[("A", 1), ("B", 2), ("C", 3)]));
        let (_, h2) = canonical_leaves(&leaves(&[("A", 1), ("B", 2), ("C", 9)]));
        let root2 = merkle_root(&h2);
        // Prove A in tree 1, check against tree 2's root: A's leaf is identical
        // but the path hashes differ, so it must fail.
        let proof = merkle_proof(&h1, 0).expect("in range");
        let (name, ch) = &o1[0];
        assert!(!verify_membership(&root2, &leaf_hash(name, ch), &proof));
    }

    #[test]
    fn receipt_within_tcb_flag_and_audit() {
        let ls = leaves(&[("thmA", 1), ("thmB", 2)]);
        let axioms = vec!["propext".to_string(), "Quot.sound".to_string()];
        // A COMPLETE axiom basis that is a subset of TCB ⇒ within_tcb Some(true).
        let (receipt, _) =
            TrustReceipt::build(&ls, &axioms, true, Some("Mathlib@abc".into()), "1.2.0");
        assert_eq!(receipt.within_tcb, Some(true), "subset of TCB ⇒ within_tcb");
        assert_eq!(receipt.leaf_count, 2);
        assert!(receipt.axiom_basis_complete);
        // Audit: re-derive from the same leaves ⇒ passes.
        assert!(receipt.verify_against_leaves(&ls, &axioms));
        // Audit with a tampered leaf set ⇒ fails (root mismatch).
        let mut tampered = ls.clone();
        tampered[0].1 = [42u8; 32];
        assert!(!receipt.verify_against_leaves(&tampered, &axioms));

        // An out-of-TCB axiom flips within_tcb to Some(false).
        let bad_axioms = vec!["propext".to_string(), "sorryAx".to_string()];
        let (bad, _) = TrustReceipt::build(&ls, &bad_axioms, true, None, "1.2.0");
        assert_eq!(
            bad.within_tcb,
            Some(false),
            "a non-TCB axiom ⇒ not within_tcb"
        );

        // An INCOMPLETE basis ⇒ within_tcb None and an empty published closure,
        // regardless of what was passed in (no partial set masquerades as basis).
        let (partial, _) = TrustReceipt::build(&ls, &axioms, false, None, "1.2.0");
        assert_eq!(partial.within_tcb, None, "incomplete basis ⇒ no TCB claim");
        assert!(
            partial.axiom_closure.is_empty(),
            "partial basis not published"
        );
        assert!(
            partial.verify_against_leaves(&ls, &axioms),
            "root still audits"
        );
    }

    #[test]
    fn receipt_json_roundtrips() {
        let ls = leaves(&[("x", 5)]);
        let (r, _) = TrustReceipt::build(&ls, &[], false, None, "1.2.0");
        let json = serde_json::to_string(&r).unwrap();
        let back: TrustReceipt = serde_json::from_str(&json).unwrap();
        assert_eq!(r, back);
        assert_eq!(
            back.root_bytes().unwrap(),
            merkle_root(&canonical_leaves(&ls).1)
        );
    }
}
