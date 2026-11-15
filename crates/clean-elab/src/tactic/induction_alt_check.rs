// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The checks Lean runs on the `with` alternatives of `cases`/`induction`
//! before and while it dispatches them (`ElimApp.evalAlts`,
//! `Lean/Elab/Tactic/Induction.lean`, v4.30.0-rc2).
//!
//! The alternatives reaching here are already expanded to one left-hand side
//! each (the parser does what Lean's `expandInductionAlts?` does), so the
//! checks read them exactly as `checkAltNames` does:
//!
//! - a `| _ => …` alternative that is not the last one is an error
//!   ("Invalid occurrence of the wildcard alternative …");
//! - a named alternative repeated is an error ("Duplicate alternative name").
//!
//! The dispatch then covers each named alternative's case and lets the
//! wildcard cover every case left. Lean refuses a named alternative that
//! covers no case — its name is not one of the eliminator's alternatives
//! (`Invalid alternative name`), or its case is unreachable
//! (`Alternative … is not needed`) — and a wildcard that is reached with no
//! eliminator alternative left ("Wildcard alternative is not needed").
//! [`assign_alternatives`] decides which alternative each case goal takes and
//! refuses a named alternative that covers no case. Clean does not keep the
//! cases its elimination proves unreachable, so it cannot tell those two Lean
//! messages apart; its refusal names both.
//!
//! The wildcard check is NOT modelled. Lean counts an unreachable case as an
//! alternative the wildcard still covers (it skips that case silently and
//! never elaborates the wildcard's right-hand side), so a wildcard over only
//! unreachable cases is accepted. Clean has dropped those cases and cannot
//! tell that wildcard from one with nothing left, so it accepts both: an
//! unneeded wildcard is a known false acceptance, kept as it was before this
//! module (PKG-U14 item 16), rather than a false refusal of Lean-valid code.

use std::collections::VecDeque;

use clean_parser::{SurfaceInductionAlt, SurfaceName};

use super::{Goal, TacticError};

/// Whether `alt` is the wildcard alternative `| _ => …`.
pub(super) fn is_wildcard(alt: &SurfaceInductionAlt) -> bool {
    !alt.explicit && alt.name.is_unescaped_component("_")
}

/// Lean's `checkAltNames`, the part that reads only the syntax: the wildcard
/// is last, and no named alternative appears twice.
pub(super) fn check_alt_names(
    tactic_name: &str,
    alts: &[SurfaceInductionAlt],
) -> Result<(), TacticError> {
    let mut seen: Vec<&SurfaceName> = Vec::new();
    for (index, alt) in alts.iter().enumerate() {
        if is_wildcard(alt) {
            if index + 1 != alts.len() {
                return Err(refusal(
                    tactic_name,
                    "Invalid occurrence of the wildcard alternative `| _ => ...`: \
                     It must be the last alternative"
                        .into(),
                ));
            }
            continue;
        }
        if seen.contains(&&alt.name) {
            return Err(refusal(
                tactic_name,
                format!("Duplicate alternative name `{}`", alt.name),
            ));
        }
        seen.push(&alt.name);
    }
    Ok(())
}

/// Whether the case goal `goal` is the case the named alternative `alt`
/// selects. A case goal's tag is its parent goal's tag with the alternative's
/// name appended (Lean's `tag ++ altName`), so the alternative names the LAST
/// component: `| cons a l` selects `some.cons` under a goal tagged `some`.
/// Lean compares the alternative's name with the eliminator's alternative
/// names, which are atomic, so a dotted alternative (`| Nat.succ n ih`)
/// selects no case.
fn selects(alt: &SurfaceInductionAlt, goal: &Goal) -> bool {
    goal.tag
        .as_ref()
        .is_some_and(|tag| tag.last_component() == alt.name)
}

/// For each case goal, in order, the index into `alts` of the alternative
/// that covers it: the first named alternative selecting it, else the
/// wildcard, else `None` (the caller reports that case as not provided).
///
/// Refuses, as Lean's dispatch does, a named alternative that covers no case.
/// A wildcard that covers no case goal is accepted (see the module doc: it may
/// cover cases the elimination dropped as unreachable). REQUIRES:
/// [`check_alt_names`] accepted `alts`, so the wildcard, if any, is last.
pub(super) fn assign_alternatives(
    tactic_name: &str,
    alts: &[SurfaceInductionAlt],
    goals: &VecDeque<Goal>,
) -> Result<Vec<Option<usize>>, TacticError> {
    let wildcard = alts.iter().rposition(is_wildcard);
    let assignment: Vec<Option<usize>> = goals
        .iter()
        .map(|goal| {
            alts.iter()
                .position(|alt| !is_wildcard(alt) && selects(alt, goal))
                .or(wildcard)
        })
        .collect();
    for (index, alt) in alts.iter().enumerate() {
        if is_wildcard(alt) || assignment.contains(&Some(index)) {
            continue;
        }
        let detail = format!(
            "Alternative `{}` covers no case of this elimination: it names no \
             alternative of the eliminator (Lean: `Invalid alternative name`) or \
             its case is unreachable (Lean: `Alternative ... is not needed`)",
            alt.name
        );
        return Err(refusal(tactic_name, detail));
    }
    Ok(assignment)
}

fn refusal(tactic_name: &str, detail: String) -> TacticError {
    TacticError::InvalidTarget {
        tactic: tactic_name.into(),
        detail,
    }
}
