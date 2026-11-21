// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The headline board in section 4 order. The catalog owns all readings
//! and absence reasons. Each numbered row lists the figures in display order.

pub(super) const BOARD: &[&[&str]] = &[
    &[
        "selfproof.decided_by_compiled_kcheck",
        "selfproof.accepted_by_kcheck_no_site",
    ],
    &[
        "selfproof.planted_false.clean",
        "selfproof.planted_false.trust",
        "selfproof.planted_false.inside_fragment",
    ],
    &["alignment.functions"],
    &["alignment.premises"],
    &["alignment.instance"],
    &["lean_model.compiled_by_trust"],
    &["compiled.kcheck_bodies"],
    &["rust_to_trustir.functions_bound"],
    &["model.lean.families", "selfproof.lean_kernel_rule_families"],
    &["selfproof.theories_elaborated"],
    &["selfproof.island_gaps", "island.pin_lag_commits"],
    &[
        "model.rust.instg_in_semr",
        "model.rust.minitests_in_core",
        "model.rust.divergence_rows_with_lemma",
        "model.rust.prod_equiv_bodies",
        "model.rust.rm_accept",
    ],
    &["model.trustir.referees"],
    &["diff.kernel"],
    &["seams"],
    &[clean_evidence::envelope::python_minters::FIGURE],
    &["evidence.stale_figures"],
];

/// The board row that shows the figure, when present.
pub(super) fn row_of(figure: &str) -> Option<u8> {
    BOARD
        .iter()
        .zip(1..)
        .find_map(|(figures, number)| figures.contains(&figure).then_some(number))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd_evidence::FIGURES;
    use std::collections::HashSet;

    #[test]
    fn test_board_rows_are_in_section_four_order() {
        assert_eq!(BOARD.len(), 17);
        assert!(BOARD.iter().all(|row| !row.is_empty()));
        assert_eq!(row_of("seams"), Some(15));
        assert_eq!(row_of("evidence.stale_figures"), Some(17));
    }

    #[test]
    fn test_board_names_each_figure_once_and_only_registered_ones() {
        let registered: HashSet<&str> = FIGURES.iter().map(|figure| figure.id).collect();
        let mut seen = HashSet::new();
        for id in BOARD.iter().flat_map(|row| row.iter().copied()) {
            assert!(registered.contains(id), "{id} is not registered");
            assert!(seen.insert(id), "{id} appears twice");
        }
        for figure in FIGURES
            .iter()
            .filter(|figure| figure.absent_reason().is_some())
        {
            assert!(
                seen.contains(figure.id),
                "{} is missing from the board",
                figure.id
            );
        }
    }
}
