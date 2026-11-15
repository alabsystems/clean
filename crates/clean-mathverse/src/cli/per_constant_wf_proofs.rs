// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The imported theorems the demand walk loads WITH their values (decision
//! R147).
//!
//! The walk parses an import types-only (`parse_dep_module_types_only`): a
//! theorem's proof body is not reconstructed, which bounds the walk's memory
//! and its closure. Lean's kernel does δ-unfold theorems, though, and a check
//! needs a proof's value wherever iota reduction needs the proof to be a
//! constructor: the major premise of a recursor that eliminates a proposition
//! into data. The ones checks reach routinely are the carriers of well-founded
//! recursion, `Acc` and `WellFounded`. Evaluating a function defined through
//! `Acc.rec` or `WellFounded.fix` unfolds the `Acc` proofs it recurses on. With
//! their values elided such a check is stuck, and an honest declaration Lean
//! accepts is refused. Measured 2026-10-19 on `ReplayIsPropStuck`:
//! `IPK.proposition` was refused (`TypeMismatch`) because `IPK.b._proof_1` and
//! `IPK.c._proof_1` were resident value-less.
//!
//! So an imported theorem whose statement concludes in `Acc` or `WellFounded`
//! is loaded with its value, and the walk descends into that value. Every other
//! imported theorem stays value-less. A check that needs one (a large
//! elimination out of `And`, `Iff` or a user's proposition, or a statement that
//! only unfolds to `Acc`) is still refused, never admitted: the fail-closed
//! direction. Trust is unchanged. An import's theorem value is trusted context
//! exactly as an import's definition value already is: neither is re-checked,
//! only the target is, the leanchecker-without-`--fresh` contract this lane
//! states.
//!
//! The values come from a parse of the declaring module WITH proofs
//! (`parse_target_module_with_proofs`). Only the module's `Acc`/`WellFounded`
//! theorems are kept and the rest of that parse is dropped at once, so the walk
//! holds one module's proof terms at a time, the bound `compute_axiom_closure`
//! keeps. A verified-shard source (the lazy lane) is unchanged: it serves what
//! its shard stores.
//!
//! That parse reads the module's `.olean` again, so it is held to the walk's
//! Lean world (R81) the way `compute_axiom_closure`'s parse is: the artifact is
//! admitted first, and a module of a refused or second world contributes no
//! value (its theorems stay value-less, the fail-closed side).

use std::collections::HashMap;
use std::path::Path;

use clean_olean::ConstantKind as OleanKind;
use clean_olean::{LeanWorldScope, ParsedConstant, ParsedExpr};

use super::{parse_target_module_with_proofs, Walker};

/// The inductive propositions well-founded recursion recurses on.
const WF_CARRIERS: [&str; 2] = ["Acc", "WellFounded"];

/// Whether `ty`, a theorem's statement, concludes in `Acc` or `WellFounded`:
/// the head of the body under its `∀` binders, read syntactically. There is no
/// δ here, so a statement that only unfolds to one of them stays value-less, the
/// fail-closed side.
pub(super) fn concludes_in_wf_carrier(ty: &ParsedExpr) -> bool {
    let mut body = ty;
    while let ParsedExpr::ForallE(_, _, inner, _) | ParsedExpr::MData(_, inner) = body {
        body = inner;
    }
    let mut head = body;
    while let ParsedExpr::App(f, _) | ParsedExpr::MData(_, f) = head {
        head = f;
    }
    matches!(head, ParsedExpr::Const(name, _) if WF_CARRIERS.contains(&name.as_str()))
}

/// Whether `constant` is a theorem that concludes in a well-founded-recursion
/// carrier.
fn is_wf_proof(constant: &ParsedConstant) -> bool {
    matches!(constant.kind, OleanKind::Theorem)
        && constant.type_.as_ref().is_some_and(concludes_in_wf_carrier)
}

impl Walker<'_> {
    /// The constant at `(olean, idx)` parsed WITH its proof, when it is an
    /// imported theorem that concludes in `Acc` or `WellFounded`. `None` for any
    /// other constant, for the target module (parsed with proofs already), for
    /// a module `world` does not admit, and when the module cannot be parsed
    /// with proofs; the caller then loads the constant as before (value-less,
    /// for a theorem).
    pub(super) fn wf_proof(
        &mut self,
        olean: &Path,
        idx: usize,
        world: &mut LeanWorldScope,
    ) -> Option<ParsedConstant> {
        if self.full_parsed.contains(olean) {
            return None;
        }
        let constant = self.parsed_constant(olean, idx)?;
        if !is_wf_proof(constant) {
            return None;
        }
        let name = constant.name.clone();
        if !self.wf_proofs.contains_key(olean) {
            let kept: HashMap<String, ParsedConstant> =
                match world.admit_artifact(&olean.display().to_string(), olean) {
                    Err(e) => {
                        eprintln!("per-constant-verify: Acc/WellFounded proof values: {e}");
                        HashMap::new()
                    }
                    Ok(()) => match parse_target_module_with_proofs(olean) {
                        Ok(module) => module
                            .constants
                            .into_iter()
                            .filter(|c| c.value.is_some() && is_wf_proof(c))
                            .map(|c| (c.name.clone(), c))
                            .collect(),
                        // The artifact rule's refusal fails the run by name
                        // (R113), as `try_ensure_parsed` records it; any other
                        // parse failure only withholds the values, a refusal.
                        Err(e) => {
                            if matches!(e, crate::error::MathverseError::ArtifactRefused { .. }) {
                                self.refused.get_or_insert_with(|| e.to_string());
                            }
                            HashMap::new()
                        }
                    },
                };
            self.wf_proofs.insert(olean.to_path_buf(), kept);
        }
        self.wf_proofs.get(olean)?.get(&name).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_olean::ParsedBinderInfo;

    fn konst(name: &str) -> ParsedExpr {
        ParsedExpr::Const(name.to_owned(), Vec::new())
    }

    fn app(f: ParsedExpr, a: ParsedExpr) -> ParsedExpr {
        ParsedExpr::App(Box::new(f), Box::new(a))
    }

    fn forall(dom: ParsedExpr, body: ParsedExpr) -> ParsedExpr {
        ParsedExpr::ForallE(
            "x".to_owned(),
            Box::new(dom),
            Box::new(body),
            ParsedBinderInfo::Default,
        )
    }

    #[test]
    fn test_concludes_in_wf_carrier_reads_the_head_under_the_binders() {
        let acc = app(app(konst("Acc"), konst("r")), ParsedExpr::BVar(0));
        assert!(concludes_in_wf_carrier(&acc));
        assert!(concludes_in_wf_carrier(&forall(konst("Nat"), acc.clone())));
        let wf = app(konst("WellFounded"), konst("r"));
        assert!(concludes_in_wf_carrier(&forall(konst("Nat"), wf)));
    }

    /// The re-parse that serves an `Acc` proof's value is held to the walk's
    /// Lean world: with the scope bound to v4.8.0's world, the pinned module's
    /// proofs are not served (a second world is refused), and with a scope
    /// that admits the pinned world they are.
    #[test]
    fn test_wf_proof_is_held_to_the_walk_world() {
        use std::collections::BTreeMap;
        use std::path::PathBuf;

        let dir = clean_olean::test_support::compiled_fixture_dir("replay_forged");
        let olean = dir.join("ReplayIsPropStuckBase.olean");
        let index = super::super::NameOleanIndex {
            oleans: Vec::new(),
            by_name: HashMap::new(),
            redeclared: BTreeMap::new(),
        };
        let wf_idx = |walker: &mut Walker<'_>| -> usize {
            assert!(walker.ensure_parsed(&olean, true), "the fixture parses");
            walker.parsed[&olean]
                .constants
                .iter()
                .position(is_wf_proof)
                .expect("ReplayIsPropStuckBase declares an Acc proof")
        };

        let mut pinned = LeanWorldScope::new();
        let mut walker = Walker::new(&dir, &index, None);
        let idx = wf_idx(&mut walker);
        let served = walker
            .wf_proof(&olean, idx, &mut pinned)
            .expect("a pinned-world module serves its Acc proof");
        assert!(served.value.is_some(), "served with its value");

        let foreign: PathBuf = [
            env!("CARGO_MANIFEST_DIR"),
            "../../tests/fixtures/olean/v4.8.0/witness/FactLib.olean",
        ]
        .iter()
        .collect();
        let mut second = LeanWorldScope::new();
        second
            .admit_olean_file("FactLib", &foreign)
            .expect("v4.8.0's world binds an empty scope");
        let mut walker = Walker::new(&dir, &index, None);
        let idx = wf_idx(&mut walker);
        assert!(
            walker.wf_proof(&olean, idx, &mut second).is_none(),
            "a module of a second world serves no proof value"
        );
        assert_eq!(walker.wf_proofs.get(&olean).map(HashMap::len), Some(0));
    }

    #[test]
    fn test_concludes_in_wf_carrier_refuses_other_conclusions() {
        let and = app(app(konst("And"), konst("p")), konst("q"));
        assert!(!concludes_in_wf_carrier(&and));
        // A hypothesis about `Acc` is not a conclusion in it.
        let acc = app(app(konst("Acc"), konst("r")), ParsedExpr::BVar(0));
        assert!(!concludes_in_wf_carrier(&forall(acc, konst("False"))));
        // A name that merely ends in `Acc` is another constant.
        assert!(!concludes_in_wf_carrier(&app(konst("Foo.Acc"), konst("r"))));
    }
}
