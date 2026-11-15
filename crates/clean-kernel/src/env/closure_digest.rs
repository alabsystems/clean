// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Canonical content digest of one declaration's transitive dependency
//! closure (two-language roadmap WS6.7(a)).
//!
//! # What it is for
//!
//! A TrustIR `CertificateBinding.source` names the source definition a
//! translation-validation comparand was derived from as
//! `SourceDefinitionRef { decl, closure_digest }`. The declaration NAME alone
//! identifies nothing: the same name means something else once any constant
//! it reaches is redefined. [`Environment::closure_digest`] is the identity of
//! what the name MEANS in this environment — every declaration it reaches,
//! byte for byte — so a certificate minted against one elaboration of `f` and
//! a client holding another can tell the two apart (WS6.8 compares exactly
//! this).
//!
//! # What is, and is not, hashed
//!
//! The closure of `n` is the least set containing `n` and closed under:
//!
//! * every constant a member's type or value mentions (the kernel's single
//!   reference walk, `axiom_audit::collect_const_refs`, so a projection's
//!   structure name counts exactly as it does for the axiom audit);
//! * an inductive type's mutual siblings (`all_names`) and constructors — the
//!   type IS what its constructors say, so adding or changing a constructor
//!   changes every definition that mentions the type;
//! * a constructor's or recursor's inductive type, and a recursor's rule
//!   constructors and right-hand sides.
//!
//! For every member, in ascending order of its canonical name bytes, the
//! preimage carries the name and all five of the kernel's records for it
//! (`ConstantInfo`, `InductiveVal`, `ConstructorVal`, `RecursorVal`,
//! `QuotVal`), each presence-prefixed. The environment's [`CleanMode`] and the
//! ROOT name are hashed too: a mutual family's members share one closure, and
//! the root is what distinguishes `closure_digest(Even)` from
//! `closure_digest(Odd)`.
//!
//! Every record is encoded with `bincode::serde` under
//! `bincode::config::standard()` — the kernel's own persisted encoding
//! (`Environment::to_bincode`, snapshots, certificate bundles), a
//! prefix-free, length-framed encoding of the serde-derived records. Levels,
//! binder data (info and multiplicity), literals, `let` names and metadata
//! are therefore all part of the preimage, and each record is itself
//! length-prefixed in the SHA-256 stream, so the framing is injective. It is
//! NEVER the kernel's `u64` cache hash (`cache.rs`, `cert/trace.rs`
//! `expr_hash`), which is a table key and collides by design.
//!
//! What this establishes: two environments give `n` the same digest only if
//! they hold byte-identical records for every declaration `n` reaches (up to
//! SHA-256). What it does not: it says nothing about the kernel's own checking
//! code (that is the build identity), and nothing about declarations `n` does
//! not reach — renaming or adding an unrelated constant leaves it unchanged.
//!
//! # Relation to TrustIR's environment digest
//!
//! The WHOLE-environment digest a TrustIR `CertificateBinding` carries
//! (`environment_digest`) is NOT defined here: WS1.12 defined it TrustIR-side
//! (`trust_ir::proof::kernel_environment_digest`, domain
//! `trust_ir.clean_cic.environment.v1`) over this crate's public iteration
//! API, so the minter and the re-checker run one function and agree by
//! construction. A second, kernel-owned environment digest would be a second
//! identity for the same thing; the roadmap's `Environment::digest()` is
//! superseded by that function and deliberately not added.
//!
//! [`CleanMode`]: crate::mode::CleanMode

use hashbrown::HashSet;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

use crate::name::Name;

use super::axiom_audit::collect_const_refs;
use super::Environment;

/// Domain string of [`Environment::closure_digest`]. Versioned: a change to
/// the member set, the record encoding or the framing is a new domain.
pub const CLOSURE_DIGEST_DOMAIN: &str = "clean_kernel.constant_closure.v1";

/// Why a closure digest could not be stated. Every variant is a refusal: a
/// closure that cannot be enumerated completely is never digested partially.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ClosureDigestError {
    /// The root is not declared in this environment.
    #[error("`{name}` is not declared in this environment")]
    UnknownDeclaration {
        /// The undeclared root.
        name: Name,
    },
    /// A member mentions a name this environment does not declare, so the
    /// closure is not closed here.
    #[error("`{member}` mentions `{missing}`, which this environment does not declare")]
    DanglingReference {
        /// The member whose type, value or record mentions `missing`.
        member: Name,
        /// The undeclared name.
        missing: Name,
    },
    /// A record failed to encode.
    #[error("the record of `{member}` does not encode: {reason}")]
    Encode {
        /// The member whose record failed.
        member: Name,
        /// The encoder's message.
        reason: String,
    },
}

/// The kernel's persisted encoding of one record.
fn encode<T: serde::Serialize>(value: &T, member: &Name) -> Result<Vec<u8>, ClosureDigestError> {
    bincode::serde::encode_to_vec(value, bincode::config::standard()).map_err(|error| {
        ClosureDigestError::Encode {
            member: member.clone(),
            reason: error.to_string(),
        }
    })
}

/// Length-prefixed (`u64`, little-endian) bytes into the digest stream.
fn put_bytes(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

/// A presence-prefixed optional record into the digest stream.
fn put_record<T: serde::Serialize>(
    hasher: &mut Sha256,
    record: Option<&T>,
    member: &Name,
) -> Result<(), ClosureDigestError> {
    match record {
        None => hasher.update([0u8]),
        Some(record) => {
            hasher.update([1u8]);
            put_bytes(hasher, &encode(record, member)?);
        }
    }
    Ok(())
}

impl Environment {
    /// Whether any of the kernel's five declaration tables holds `name`
    /// (constants, including a lazily-served one; inductives; constructors;
    /// recursors; quotient primitives).
    fn declares_for_closure(&self, name: &Name) -> bool {
        self.get_const(name).is_some()
            || self.get_inductive(name).is_some()
            || self.get_constructor(name).is_some()
            || self.get_recursor(name).is_some()
            || self.get_quot(name).is_some()
    }

    /// The names one closure member reaches directly (see the module docs for
    /// the edge set).
    fn closure_edges(&self, member: &Name) -> HashSet<Name> {
        let mut out = HashSet::new();
        if let Some(info) = self.get_const(member) {
            collect_const_refs(&info.type_, &mut out);
            if let Some(value) = &info.value {
                collect_const_refs(value, &mut out);
            }
        }
        if let Some(inductive) = self.get_inductive(member) {
            collect_const_refs(&inductive.type_, &mut out);
            out.extend(inductive.all_names.iter().cloned());
            out.extend(inductive.constructor_names.iter().cloned());
        }
        if let Some(constructor) = self.get_constructor(member) {
            collect_const_refs(&constructor.type_, &mut out);
            out.insert(constructor.inductive_name.clone());
        }
        if let Some(recursor) = self.get_recursor(member) {
            collect_const_refs(&recursor.type_, &mut out);
            out.insert(recursor.inductive_name.clone());
            for rule in &recursor.rules {
                out.insert(rule.constructor_name.clone());
                collect_const_refs(&rule.rhs, &mut out);
            }
        }
        if let Some(quot) = self.get_quot(member) {
            collect_const_refs(&quot.type_, &mut out);
        }
        out
    }

    /// The transitive dependency closure of `name` (including `name`), in
    /// ascending order of each member's canonical name bytes — the order
    /// [`Self::closure_digest`] hashes them in.
    ///
    /// # Errors
    ///
    /// [`ClosureDigestError::UnknownDeclaration`] when `name` is not declared,
    /// [`ClosureDigestError::DanglingReference`] when a member mentions an
    /// undeclared name (reported for the smallest such pair, so the refusal
    /// does not depend on hash iteration order), and
    /// [`ClosureDigestError::Encode`] when a name does not encode.
    pub fn dependency_closure(&self, name: &Name) -> Result<Vec<Name>, ClosureDigestError> {
        if !self.declares_for_closure(name) {
            return Err(ClosureDigestError::UnknownDeclaration { name: name.clone() });
        }
        // Keyed by canonical name bytes: a total, injective order that does not
        // depend on how a name prints (two distinct names can print alike).
        let mut members: BTreeMap<Vec<u8>, Name> = BTreeMap::new();
        let mut work = vec![name.clone()];
        while let Some(member) = work.pop() {
            let key = encode(&member, &member)?;
            if members.contains_key(&key) {
                continue;
            }
            let mut edges: Vec<(Vec<u8>, Name)> = self
                .closure_edges(&member)
                .into_iter()
                .map(|edge| encode(&edge, &member).map(|bytes| (bytes, edge)))
                .collect::<Result<_, _>>()?;
            edges.sort_by(|a, b| a.0.cmp(&b.0));
            if let Some((_, missing)) = edges
                .iter()
                .find(|(_, edge)| !self.declares_for_closure(edge))
            {
                return Err(ClosureDigestError::DanglingReference {
                    member,
                    missing: missing.clone(),
                });
            }
            members.insert(key, member);
            work.extend(
                edges
                    .into_iter()
                    .filter(|(bytes, _)| !members.contains_key(bytes))
                    .map(|(_, edge)| edge),
            );
        }
        Ok(members.into_values().collect())
    }

    /// SHA-256 content digest of `name`'s transitive dependency closure under
    /// the domain [`CLOSURE_DIGEST_DOMAIN`] (roadmap WS6.7(a)). See the module
    /// docs for exactly what is hashed and what that establishes.
    ///
    /// Works on an environment with a lazy constant source too: a lazily
    /// served member is materialized through [`Self::get_const`], exactly as
    /// the kernel would read it.
    ///
    /// # Errors
    ///
    /// As [`Self::dependency_closure`]; a closure that cannot be enumerated
    /// completely is refused, never digested partially.
    pub fn closure_digest(&self, name: &Name) -> Result<[u8; 32], ClosureDigestError> {
        let members = self.dependency_closure(name)?;
        let mut hasher = Sha256::new();
        put_bytes(&mut hasher, CLOSURE_DIGEST_DOMAIN.as_bytes());
        put_bytes(&mut hasher, &encode(&self.mode(), name)?);
        put_bytes(&mut hasher, &encode(name, name)?);
        hasher.update((members.len() as u64).to_le_bytes());
        for member in &members {
            put_bytes(&mut hasher, &encode(member, member)?);
            put_record(&mut hasher, self.get_const(member), member)?;
            put_record(&mut hasher, self.get_inductive(member), member)?;
            put_record(&mut hasher, self.get_constructor(member), member)?;
            put_record(&mut hasher, self.get_recursor(member), member)?;
            put_record(&mut hasher, self.get_quot(member), member)?;
        }
        Ok(hasher.finalize().into())
    }
}

#[cfg(test)]
#[path = "closure_digest_tests.rs"]
mod tests;
