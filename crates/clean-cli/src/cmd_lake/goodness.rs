// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake goodness` — a constant's Cake profile.
//!
//! Loads the `.olean` environment and reports, for one constant: its semantic identity
//! (structural / defeq-canonical / Tier-1.5 rewrite-canonical digests), its proof goodness
//! (`G` mass + `F` weakest-link floor — the per-theorem **bedrock-distance** from the 3
//! foundational axioms), and its derivation complexity. The queryable "how good / how far
//! from the 3 axioms" tool — a dimension Lean 4 has no analog for.

use std::path::PathBuf;

pub(super) fn lake_goodness(
    module: Vec<String>,
    olean_search_path: Vec<PathBuf>,
    constant: String,
    json: bool,
) -> anyhow::Result<()> {
    if module.is_empty() {
        anyhow::bail!("goodness: at least one --module is required");
    }
    if olean_search_path.is_empty() {
        anyhow::bail!("goodness: at least one --olean-search-path is required");
    }

    let mut env = clean_kernel::Environment::default();
    for m in &module {
        eprintln!("[goodness] loading {m} …");
        clean_olean::load_module_with_deps(&mut env, m, &olean_search_path)
            .map_err(|e| anyhow::anyhow!("loading module `{m}`: {e}"))?;
    }

    let name = clean_kernel::Name::from_string(&constant);
    let type_ = env
        .get_const(&name)
        .ok_or_else(|| anyhow::anyhow!("constant `{constant}` is not in the loaded environment"))?
        .type_
        .clone();

    let tc = clean_kernel::tc::TypeChecker::new(&env);
    let identity = clean_cake::identity::defeq_canonical_digest(&tc, &type_);
    let goodness = clean_cake::goodness::closure_goodness(&env, &name)
        .ok_or_else(|| anyhow::anyhow!("closure_goodness: `{constant}` vanished"))?;
    let complexity = clean_cake::complexity::proof_complexity(&env, &name)
        .ok_or_else(|| anyhow::anyhow!("proof_complexity: `{constant}` vanished"))?;

    if json {
        let v = serde_json::json!({
            "constant": constant,
            "identity": {
                "structural_digest": identity.structural_digest,
                "canonical_digest": identity.canonical_digest,
                "rewrite_digest": identity.rewrite_digest,
                "complete": identity.complete,
            },
            "goodness": {
                "g_mass": goodness.g_mass,
                "normalized": goodness.normalized(),
                "floor": format!("{:?}", goodness.floor),
                "is_foundational": goodness.is_foundational(),
                "closure_size": goodness.closure_size,
                "domain_axioms": goodness.domain_axioms,
                "trust_markers": goodness.trust_markers,
            },
            "complexity": {
                "term_size": complexity.term_size,
                "term_depth": complexity.term_depth,
                "distinct_lemmas": complexity.distinct_lemmas,
            },
        });
        println!("{}", serde_json::to_string_pretty(&v)?);
    } else {
        println!("Cake profile — {constant}");
        println!(
            "  identity   : canonical {} / rewrite {} (complete={})",
            identity.canonical_digest, identity.rewrite_digest, identity.complete
        );
        println!(
            "  goodness   : G={:.2} (norm {:.3}), floor={:?}, bedrock={}, closure={}",
            goodness.g_mass,
            goodness.normalized(),
            goodness.floor,
            goodness.is_foundational(),
            goodness.closure_size
        );
        if !goodness.domain_axioms.is_empty() {
            println!("    domain axioms : {}", goodness.domain_axioms.join(", "));
        }
        if !goodness.trust_markers.is_empty() {
            println!("    TRUST MARKERS : {}", goodness.trust_markers.join(", "));
        }
        println!(
            "  complexity : term_size={}, depth={}, distinct_lemmas={}",
            complexity.term_size, complexity.term_depth, complexity.distinct_lemmas
        );
    }
    Ok(())
}
