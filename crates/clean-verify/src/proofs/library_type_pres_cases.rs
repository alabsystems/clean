// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type preservation case-analysis proof-LIBRARY entries.
//!
//! Covers: type_preservation_cases.rs, type_preservation_cases_def_eq.rs,
//! and type_preservation_cases_congruence.rs spec definitions.
//!
//! Brick 9 (#2859): these library entries are MIRRORS of the corresponding spec
//! definitions, whose `value_src` carries the canonical, kernel-checked proof
//! term (validated by `build_spec_with_stack` and the provenance gates). The
//! former hand-duplicated proof terms had drifted out of sync with the spec
//! (missing the `RedEnvFaithful the_red_env` hypotheses added by the
//! church_rosser_whnf retirement) and several rested on the FALSE `def_eq_to_eq`
//! bridge that Brick 9 deleted. Each entry now delegates to its spec constant —
//! a closed term of exactly the property type — so the library audit reflects the
//! spec proof directly with ZERO references to the deleted `def_eq_to_eq`.
//!
//! Part of #2859, #3221.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_type_pres_cases_proofs(&mut self) {
        // (property name, explanation). The proof term is the spec constant of the
        // same name (its value_src carries the kernel-checked proof). Brick 9
        // rerouted every one of these off the deleted FALSE def_eq_to_eq bridge.
        for (name, explanation) in [
            (
                "lam_typing_body_subst",
                "Lambda typing inversion + substitution: if (lam A.b) : Pi(A0).B0 and a : A0, \
                 then b[a/0] : B0[a/0]. Mirrors the spec proof (Typing.conv + pi_injectivity_def_eq).",
            ),
            (
                "beta_preservation",
                "Beta preservation: (lam A.b) a : T implies b[a/0] : T. Mirrors the spec proof \
                 (Typing.rec + lam_typing_body_subst).",
            ),
            (
                "typing_same_term_types_def_eq",
                "Type uniqueness up to DefEq: if e : T1 and e : T2, then DefEq T1 T2. Mirrors the \
                 spec proof (Typing.rec; sort case via sort_def_eq_eq).",
            ),
            (
                "beta_expansion",
                "Typed beta expansion: rebuild (lam A.body) arg : T from component typings. \
                 Mirrors the spec proof (Typing.conv + typing_same_term_types_def_eq).",
            ),
            (
                "def_eq_typing_iff",
                "Bidirectional type preservation via TypedDefEq.rec with AndType motive. Mirrors \
                 the spec proof.",
            ),
            (
                "app_type_preservation",
                "Application type preservation: congruence preserves typing (forward). Mirrors the \
                 spec proof (Typing.conv + def_eq_instantiate_arg_congr).",
            ),
            (
                "lam_type_preservation",
                "Lambda type preservation: congruence preserves typing (forward). Mirrors the spec \
                 proof (Typing.conv + DefEq.pi_cong).",
            ),
            (
                "app_type_preservation_inv",
                "Application type preservation (reverse): congruence backwards preserves typing. \
                 Mirrors the spec proof.",
            ),
            (
                "lam_type_preservation_inv",
                "Lambda type preservation (reverse): congruence backwards preserves typing. Mirrors \
                 the spec proof.",
            ),
        ] {
            self.proofs
                .insert(name.to_string(), ProofTerm::new(name, name, explanation));
        }
    }
}
