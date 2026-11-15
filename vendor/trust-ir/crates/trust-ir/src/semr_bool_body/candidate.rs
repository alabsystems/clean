// Copyright 2026 Andrew Yates. Apache-2.0.
//! Untrusted proof candidates over the original decoder and whole-body theorem.
use super::{BoolBodyReader, Refusal};
use crate::FuncId;
use std::collections::BTreeSet;

impl BoolBodyReader<'_> {
    /// Propose original-language proofs for the actual module byte subject.
    ///
    /// The caller supplies its once-serialized actual module bytes. This method
    /// neither reserializes nor claims their association with a Rust source.
    /// An independent consumer must construct its expected goal from its own
    /// actual bytes and function identity, and kernel-check the candidate.
    /// Source names, successful emission and matching hashes grant no authority.
    ///
    /// One byte literal is shared by all requested bodies. All model values
    /// come from the original decoder; there is no reconstructed evaluator,
    /// authored substitute module, successful-decode assumption or fallback.
    pub fn candidate_source(
        &self,
        actual_module_bytes: &[u8],
        functions: &[FuncId],
    ) -> Result<String, Refusal> {
        if functions.is_empty() {
            return Err(Refusal::EmptyRequest);
        }
        let mut seen = BTreeSet::new();
        for function in functions {
            if !seen.insert(*function) {
                return Err(Refusal::DuplicateRequest);
            }
            self.derive(*function)?;
        }
        let literal = actual_module_bytes
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let mut source = format!(
            "import SemRBoolBodyChecker\nnamespace SemR.BoolBodyCandidate\ndef bytes : List Nat := [{literal}]\ntheorem decoded_success : (decode bytes).toOption.isSome = true := by decide +kernel\ndef subject : Module := (decode bytes).toOption.get decoded_success\n"
        );
        for function in functions {
            let fid = function.index();
            source.push_str(&format!("theorem accepted_{fid} : (SemR.BoolBody.checkConjunction subject {fid}).isSome = true := by decide +kernel"));
            source.push('\n');
            source.push_str(&format!("theorem correct_{fid} (a b : Bool) (depth : Nat) : runBlob bytes {fid} [.bool a, .bool b] 2 depth = .ok (.ret [.bool (a && b)]) := SemR.BoolBody.checked_blob decoded_success accepted_{fid} a b depth"));
            source.push('\n');
            source.push_str(&format!("def AndGoal_{fid} : Prop := ∀ (a b : Bool) (depth : Nat), runBlob bytes {fid} [.bool a, .bool b] 2 depth = .ok (.ret [.bool (a && b)])"));
            source.push('\n');
            source.push_str(&format!("def OrGoal_{fid} : Prop := ∀ (a b : Bool) (depth : Nat), runBlob bytes {fid} [.bool a, .bool b] 2 depth = .ok (.ret [.bool (a || b)])"));
            source.push('\n');
            source.push_str(&format!("theorem wrong_counterexample_{fid} : ¬ OrGoal_{fid} := by\n  intro wrong\n  have impossible := wrong true false 0\n  rw [correct_{fid}] at impossible\n  cases impossible"));
            source.push('\n');
        }
        source.push_str("end SemR.BoolBodyCandidate\n");
        Ok(source)
    }
}
