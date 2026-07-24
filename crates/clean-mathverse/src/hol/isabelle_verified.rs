// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native **kernel-verified** import of HOL/Isabelle proof objects into a
//! `.mathverse` shard.
//!
//! Unlike the statement-only Isabelle import (`isabelle_shard`, which stores
//! `SourceVerified` with `NO_VALUE`), this path carries the **proof term**: each
//! HOL primitive proof object is translated to a clean kernel `Expr` proof
//! ([`clean_kernel::hol_light_import`]) and **re-checked by clean's own kernel**
//! via the checking `add_decl` path. A declaration is written as
//! [`ImportConfidence::KernelVerified`] **only if**:
//!
//! 1. clean's kernel `add_decl` accepts the proof (`value : type`), and
//! 2. the proof's transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`
//!    (`propext`, `Quot.sound`, `Classical.choice`).
//!
//! The lowered shard carries the proof **value** (not `NO_VALUE`), so the
//! corpus re-verifier (`verify_corpus_incremental`) re-checks it independently.
//! Nothing is stamped `KernelVerified` that the kernel did not accept.

use clean_kernel::env::is_foundational_axiom;
use clean_kernel::hol_light_import::import_proof_object_json;
use clean_kernel::Environment;

use super::opentheory_shard::lower_kernel_expr;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
};

/// Outcome of a native verified import batch.
#[derive(Clone, Debug, Default)]
pub struct VerifiedHolImport {
    /// Declarations the kernel accepted and that reduce to the 3 axioms — these
    /// were written to the shard as `KernelVerified`.
    pub kernel_verified: usize,
    /// Proof objects the kernel rejected (translation or `add_decl` failure, or
    /// a non-foundational axiom in the closure) — not written.
    pub rejected: usize,
    /// Names of the kernel-verified declarations written.
    pub names: Vec<String>,
}

/// Verify each HOL/Isabelle proof object with clean's kernel and write the
/// genuinely-verified ones to `writer` as `KernelVerified` (with proof value).
///
/// This is intentionally conservative: a proof object is dropped (counted in
/// `rejected`) the moment the kernel declines it, so the shard only ever gains
/// honestly kernel-verified theorems.
#[must_use]
pub fn import_verified_hol_proofs(
    proof_jsons: &[&str],
    writer: &mut ShardWriter,
) -> VerifiedHolImport {
    let mut out = VerifiedHolImport::default();

    for json in proof_jsons {
        let Ok(translated) = import_proof_object_json(json) else {
            out.rejected += 1;
            continue;
        };

        // Re-check the proof against a fresh prelude environment.
        let mut env = Environment::with_prelude();
        for decl in &translated.support_declarations {
            // Support decls may already exist in the prelude; ignore those.
            let _ = env.add_decl(decl.clone());
        }
        if env.add_decl(translated.theorem_declaration()).is_err() {
            out.rejected += 1;
            continue;
        }

        // Gate on axiom closure ⊆ FOUNDATIONAL_AXIOMS (the 3 + quotient prims).
        let reducible_to_three = match env.axiom_deps(&translated.theorem_name) {
            Some(deps) => deps.iter().all(is_foundational_axiom),
            None => false,
        };
        if !reducible_to_three {
            out.rejected += 1;
            continue;
        }

        // Verified — lower the type AND the proof value, stamp KernelVerified.
        let name = translated.theorem_name.to_string();
        let name_idx = writer.add_string(&name);
        let type_idx = lower_kernel_expr(&translated.theorem_type, writer);
        let value_idx = lower_kernel_expr(&translated.proof, writer);

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Isabelle as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::Logic as u8,
            decl_kind: DeclKind::Theorem as u8,
            // Reducible to the 3 foundational axioms → no domain-axiom bits set.
            axiom_profile: AxiomProfile(0),
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };
        writer.add_constant(header);
        out.kernel_verified += 1;
        out.names.push(name);
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardReader;

    // The COMPLETE HOL/Isabelle primitive inference basis — all six rules verify
    // to the 3 axioms (see clean-kernel verified_e2e_tests).
    const REFL: &str = r#"{"name":"isa.refl","proof":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}}}"#;
    const TRANS: &str = r#"{"name":"isa.trans","proof":{"rule":"trans",
        "left":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}},
        "right":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}}}}"#;
    const BETA: &str = r#"{"name":"isa.beta","proof":{"rule":"beta",
        "binder":{"name":"x","ty":{"kind":"var","name":"a"}},
        "body":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}},
        "argument":{"kind":"var","name":"y","ty":{"kind":"var","name":"a"}}}}"#;
    const MKCOMB: &str = r#"{"name":"isa.mk_comb","proof":{"rule":"mk_comb",
        "function":{"rule":"refl","term":{"kind":"var","name":"f","ty":{"kind":"fun","domain":{"kind":"var","name":"a"},"codomain":{"kind":"var","name":"b"}}}},
        "argument":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}}}}"#;
    const ABS: &str = r#"{"name":"isa.abs","proof":{"rule":"abs",
        "binder":{"name":"x","ty":{"kind":"var","name":"a"}},
        "proof":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}}}}"#;
    const ASSUME: &str = r#"{"name":"isa.assume","proof":{"rule":"assume","proposition":{"kind":"var","name":"p","ty":{"kind":"bool"}}}}"#;
    const EQMP: &str = r#"{"name":"isa.eq_mp","proof":{"rule":"eq_mp","equality":{"rule":"refl","term":{"kind":"var","name":"p","ty":{"kind":"bool"}}},"proof":{"rule":"assume","proposition":{"kind":"var","name":"p","ty":{"kind":"bool"}}}}}"#;
    const DEDUCT: &str = r#"{"name":"isa.deduct","proof":{"rule":"deduct_antisym","left":{"rule":"assume","proposition":{"kind":"var","name":"p","ty":{"kind":"bool"}}},"right":{"rule":"assume","proposition":{"kind":"var","name":"p","ty":{"kind":"bool"}}}}}"#;
    const INST: &str = r#"{"name":"isa.inst","proof":{"rule":"inst","proof":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}},"substitutions":[{"variable":{"name":"x","ty":{"kind":"var","name":"a"}},"replacement":{"kind":"var","name":"y","ty":{"kind":"var","name":"a"}}}]}}"#;
    const INSTTYPE: &str = r#"{"name":"isa.inst_type","proof":{"rule":"inst_type","proof":{"rule":"refl","term":{"kind":"var","name":"x","ty":{"kind":"var","name":"a"}}},"substitutions":[{"variable":"a","replacement":{"kind":"bool"}}]}}"#;

    #[test]
    fn writes_kernel_verified_theorems_to_shard() {
        let mut writer = ShardWriter::new();
        let result = import_verified_hol_proofs(
            &[
                REFL, TRANS, BETA, MKCOMB, ABS, ASSUME, EQMP, DEDUCT, INST, INSTTYPE,
            ],
            &mut writer,
        );

        assert_eq!(
            result.kernel_verified, 10,
            "the full primitive basis should verify"
        );
        assert_eq!(result.rejected, 0);
        assert_eq!(result.names.len(), 10);

        // Round-trip the shard and confirm the stamps persisted as KernelVerified.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");
        assert_eq!(reader.header.constant_count, 10);

        // Look up by the actual (bridge-mangled) names that were written.
        for name in &result.names {
            let (_, hdr) = reader
                .lookup_name(name)
                .unwrap_or_else(|| panic!("missing {name}"));
            assert_eq!(
                hdr.import_confidence,
                ImportConfidence::KernelVerified as u8,
                "{name} must be stamped KernelVerified",
            );
            // Proof value present (re-checkable), not an axiom skeleton.
            assert!(hdr.has_value(), "{name} must carry a proof value");
            assert_eq!(hdr.source_system, SourceSystem::Isabelle as u8);
        }
    }

    #[test]
    fn rejects_unverifiable_proof_objects() {
        // Malformed JSON → rejected, nothing written.
        let mut writer = ShardWriter::new();
        let result = import_verified_hol_proofs(&["{ not valid"], &mut writer);
        assert_eq!(result.kernel_verified, 0);
        assert_eq!(result.rejected, 1);
    }
}
