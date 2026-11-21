// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `kernel_core_red_env` — Front #1 Stage 2 artifact (the_red_env discharge
//! program): the MECHANICALLY REFLECTED foundation-core kernel environment,
//! registered as a value-ful `RedEnv` definition. As of Front #1 STAGE 3 it
//! is the VALUE of `the_red_env` itself (`the_red_env :=
//! kernel_core_red_env`, a value-level alias — see `the_red_env.rs`), so this
//! stage registers in EVERY bundle containing `the_red_env`, immediately
//! before it. Registration replays the generated def script: the `kcre_nat_*`
//! unary pool and the `kcre_name_*` interned-name constants (depth-bounded
//! helper defs forced by the parser's measured `MAX_EXPR_DEPTH = 128` guard),
//! then the env term.
//!
//! The script is GENERATED — never hand-written — by the
//! `red_env_reflect` bin (`clean_verify::red_env_reflect`), which walks the
//! artifact-independent foundation seed (then validates against the full
//! `Specification`) and reflects the
//! foundation-core allowlist (the very inductives/definitions the modeled
//! fragment itself is written in: Nat, Bool, Eq, Name, KExpr, ListType,
//! OptionType, Lt/Le, ProdType/AndType, Level, the RecEnv-model family, and
//! the modeled fragment's function vocabulary) into the spec's
//! RecEnv/DefEnv/IndCtorEnv shape:
//!
//! - each kernel `RecursorVal` becomes `RecEnv.addRec` with its REAL
//!   (params, motives, minors, indices) counts and one `RecRule.mk` per REAL
//!   `RecursorRule` — constructor name interned, `num_fields` copied, rhs =
//!   the real rule rhs translated node-for-node;
//! - each allowlisted kernel definition value becomes `DefEnv.addDef`.
//! - each selected actual inductive/constructor record contributes its stored
//!   signature and projection-relevant counts, identities and ordered names to
//!   `IndCtorEnv`; the same signatures feed a finite `KDeclEnv`. This data
//!   extension does not itself add projection reduction or prove admission.
//!
//! ## The three encoding trust edges (full docs: `red_env_reflect` module)
//!
//! 1. **Name interning** — real string names -> `Name.str Name.anonymous
//!    <unary Nat tag>` via the emitted INJECTIVE table
//!    (`generated/kernel_core_red_env.interning.tsv`).
//! 2. **Structural levels** — sort levels, constant universe arguments and
//!    ordered schematic signatures retain zero/succ/max/imax/param trees.
//!    Guarded iota/delta use the actual head universe list. This is not a
//!    correspondence proof for Rust's smart universe normalization.
//! 3. **Bounded coverage** — Quot rules, the K extension, structure
//!    eta/projection, native reducers and literal constructor normalization
//!    are outside the selected syntactic rule-tail image. Unsupported required
//!    nodes refuse reflection; explicit behavior exclusions are in the ledger
//!    (`generated/kernel_core_red_env.skips.md`).
//!
//! ## Fidelity gate
//!
//! `tests/kernel_core_red_env_fidelity.rs` re-walks the live kernel env and
//! compares the regenerated reflection 1:1 (rule-for-rule, field-for-field on
//! the structurally reflected image) against the committed artifacts; any drift — a kernel
//! recursor change, a definition value change, an allowlist edit without
//! regeneration — fails the gate. Regenerate with:
//! the canonical Trust `targo --unverified run --locked --release -p clean-verify --bin red_env_reflect` lane.
//!
//! ## Census / masquerade posture
//!
//! `kernel_core_red_env` is a value-ful `def` (lowers to
//! `Declaration::Definition`) — census-NEUTRAL (stays 11). NO property of it
//! is axiomatized here; interface discharges over it live in the designated
//! checker modules (`env_closed_checkers_depth.rs` payoff witnesses,
//! `faithful_checkers.rs` Stage-4 discharge). Nothing carried is replaced by
//! THIS stage.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The generated def SCRIPT (one Lean-syntax `def` per line: the `kcre_nat_*`
/// unary pool, the `kcre_name_*` interned-name constants, generated semantic
/// non-vacuity witness helpers, then the `kernel_core_red_env : RedEnv` term
/// with atom leaves — the shape forced by the parser's measured
/// `MAX_EXPR_DEPTH = 128` guard).
/// GENERATED FILE — do not edit by hand; regenerate with the
/// `red_env_reflect` bin. The fidelity gate pins it to the live kernel env.
const KERNEL_CORE_RED_ENV_SCRIPT: &str = include_str!("generated/kernel_core_red_env.defs.txt");

impl Specification {
    /// Register the reflected foundation-core environment
    /// `kernel_core_red_env` (since Front #1 Stage 3, the VALUE of
    /// `the_red_env` — registered immediately before it), by replaying the
    /// generated def script in order. Every line is a value-ful `def`
    /// (census-neutral).
    pub(super) fn add_kernel_core_red_env(&mut self) -> Result<(), SpecError> {
        if let Some(script) = self.red_env_script_override.take() {
            self.add_kernel_core_red_env_script(&script)
        } else {
            self.add_kernel_core_red_env_script(KERNEL_CORE_RED_ENV_SCRIPT)
        }
    }

    /// Replay a generated red-environment script.
    ///
    /// Kept separate from the committed include so the generator can validate
    /// a fresh in-memory script against an artifact-independent seed before
    /// publishing it.
    pub(super) fn add_kernel_core_red_env_script(&mut self, script: &str) -> Result<(), SpecError> {
        for (line_index, line) in script.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let description = if line.starts_with("def kernel_core_red_env") {
                "MECHANICALLY REFLECTED foundation-core kernel environment (Front #1 Stage 2): \
                 the real recursors (real RecMeta counts and structurally level-preserving rule rhs) and real \
                 definition values of the inductives/defs the modeled fragment itself is written \
                 in, reflected from an artifact-independent foundation seed and validated against the full Specification by the \
                 red_env_reflect generator under the three documented trust edges (injective \
                 name interning; structural levels; bounded-coverage ledger). Since Front #1 \
                 Stage 3 this IS the value of the_red_env (value-level alias, next stage). \
                 Value-ful Definition: census-neutral. Pinned 1:1 to the kernel env by the \
                 fidelity gate (tests/kernel_core_red_env_fidelity.rs)."
            } else if [
                "def kcre_nat_type_signature ",
                "def kcre_nat_zero_signature ",
                "def kcre_nat_succ_signature ",
                "def kcre_nat_rec_signature ",
                "def kcre_nat_tenv ",
            ]
            .iter()
            .any(|prefix| line.starts_with(prefix))
            {
                "Generated finite Nat typing-data slice: four actual ConstantInfo signatures \
                 preserve structural source names, ordered universe parameters and structural \
                 types, cross-checked against source family metadata. No delta body is invented \
                 for these value-less entries. This is source-data agreement, not \
                 a formal soundness proof of the source builder's metadata, rule-payload and \
                 strict declaration checks preceding FullKernelCheck, or Rust refinement."
            } else if line.starts_with("def kcre_nat_") {
                "Generated unary-Nat helper for kernel_core_red_env (Front #1 Stage 2): one \
                 depth-2 step of the kcre_nat_* pool backing the reflected env's Nat leaves \
                 (interning tags, RecMeta counts, field counts, bvar indices, sort depths). \
                 Exists because the parser's MAX_EXPR_DEPTH=128 guard rejects the fully-inlined \
                 unary literal (measured depth 163). Value-ful def: census-neutral."
            } else if [
                "def kcre_ind_",
                "def kcre_ctor_",
                "def kcre_prod_",
                "def kcre_eq_",
            ]
            .iter()
            .any(|prefix| line.starts_with(prefix))
            {
                "Generated actual-source inductive/constructor metadata, shared stored signatures, \
                 finite typing table, or source-name alias. Ordered parameters, structural types, \
                 counts, identities, ordered constructor names, and the final stored ordered \
                 block are captured from live kernel records. That stored block is not asserted \
                 to equal the earlier pre-restoration strict context. These transparent data \
                 definitions do not prove admission or Rust refinement."
            } else if line.starts_with("def kcre_witness_prod_") {
                "Generated structural image of a nonempty actual ProdType constructor application \
                 and its source-inferred type. The live reflector checks the source application \
                 before emitting these transparent data definitions. This finite execution check \
                 is not a theorem about Rust inference."
            } else if line.starts_with("def kcre_witness_") {
                "Generated semantic non-vacuity helper for kernel_core_red_env: the reflected \
                 complete Nat.rec/Nat.zero redex or reduct, or a real reflected delta head/value. \
                 The iota pair is constructed from live RecMeta counts and the selected rule, \
                 so no consumer duplicates the recursor spine shape. Generated from the same \
                 Reflection object as kernel_core_red_env; value-ful and census-neutral."
            } else {
                "Generated interned-name constant for kernel_core_red_env (Front #1 Stage 2, \
                 trust edge 1): kcre_name_<tag> := Name.str Name.anonymous kcre_nat_<tag>, the \
                 spec Name image of one real kernel name under the INJECTIVE interning table \
                 (generated/kernel_core_red_env.interning.tsv; real name in the line comment). \
                 Value-ful def: census-neutral."
            };
            self.add_recursive_def(line, description)
                .map_err(|error| match error {
                    SpecError::ElabError(message) => SpecError::ElabError(format!(
                        "generated reflection declaration `{}` at line {}: {message}",
                        line.split_whitespace().nth(1).unwrap_or("<unnamed>"),
                        line_index + 1,
                    )),
                    other => other,
                })?;
        }
        Ok(())
    }
}
