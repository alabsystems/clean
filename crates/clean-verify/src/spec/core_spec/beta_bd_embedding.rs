// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `beta_reduces_bd ⊆ beta_reduces` — the first named sub-goal of link 4 of the
//! def-eq completeness chain.
//!
//! Link 4 (fuel adequacy) needs the algorithm's own step relation to be bounded
//! by the order `below` descends on. `below`'s `red` arm is over `whnf_step`
//! (`whnf_reduction.rs:364`, `:137`), while the algorithm runs `whnf_red_step`
//! (`whnf_progress.rs:4219`). Bridging the two decomposes into five arms, of
//! which this is the first and the only purely mechanical one.
//!
//! The two relations are the **same fifteen constructors minus one**:
//! `beta_reduces_bd` is `beta_reduces` with the `iota` arm dropped
//! (`par_reduction.rs:4278` says so, and the signatures confirm it — every
//! remaining constructor is byte-identical up to the relation name). So the
//! embedding is a 14-arm `beta_reduces_bd.rec` in which each arm applies the
//! identically-named `beta_reduces` constructor to the recursor's induction
//! hypothesis. There is no content beyond the transcription; the content of
//! link 4 lives in `whnf_red_step`'s `app_left` arm, which needs spine
//! reasoning about `delta_reduct` and is **not** addressed here.
//!
//! Worth recording because it is easy to misread the direction: `whnf_step` is
//! *not* the narrow β+δ relation its name suggests. Through `beta_reduces` it
//! already carries ι, ζ, `proj` and every congruence, which is why four of the
//! five arms of the eventual containment are constructor maps rather than
//! proofs.
//!
//! `DerivedProved`, empty axiom closure.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The fourteen `beta_reduces_bd` constructors, in recursor minor-premise
/// order: `(name, binder list, recursive-field IH pairs, applied arguments)`.
/// `beta` and `zeta` are the two non-recursive arms.
type BdArm = (&'static str, &'static str, &'static str, &'static str);

const BD_ARMS: [BdArm; 14] = [
    // name, binders, IH binder (empty for non-recursive), constructor args
    (
        "beta",
        "(bA : KExpr) (body : KExpr) (arg : KExpr)",
        "",
        "bA body arg",
    ),
    (
        "app_left",
        "(f : KExpr) (f2 : KExpr) (a : KExpr)",
        "f f2",
        "f f2 a ih",
    ),
    (
        "app_right",
        "(f : KExpr) (a : KExpr) (a2 : KExpr)",
        "a a2",
        "f a a2 ih",
    ),
    (
        "lam_ty",
        "(ty : KExpr) (ty2 : KExpr) (body : KExpr)",
        "ty ty2",
        "ty ty2 body ih",
    ),
    (
        "lam_body",
        "(ty : KExpr) (body : KExpr) (body2 : KExpr)",
        "body body2",
        "ty body body2 ih",
    ),
    (
        "pi_dom",
        "(dom : KExpr) (dom2 : KExpr) (body : KExpr)",
        "dom dom2",
        "dom dom2 body ih",
    ),
    (
        "pi_cod",
        "(dom : KExpr) (body : KExpr) (body2 : KExpr)",
        "body body2",
        "dom body body2 ih",
    ),
    (
        "forall_congr_dom",
        "(dom : KExpr) (dom2 : KExpr) (body : KExpr)",
        "dom dom2",
        "dom dom2 body ih",
    ),
    (
        "forall_congr_cod",
        "(dom : KExpr) (body : KExpr) (body2 : KExpr)",
        "body body2",
        "dom body body2 ih",
    ),
    (
        "zeta",
        "(ty : KExpr) (val : KExpr) (body : KExpr)",
        "",
        "ty val body",
    ),
    (
        "let_ty",
        "(ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr)",
        "ty ty2",
        "ty ty2 val body ih",
    ),
    (
        "let_val",
        "(ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr)",
        "val val2",
        "ty val val2 body ih",
    ),
    (
        "let_body",
        "(ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr)",
        "body body2",
        "ty val body body2 ih",
    ),
    (
        "proj",
        "(s : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr)",
        "sub sub2",
        "s i sub sub2 ih",
    ),
];

impl Specification {
    /// Register `beta_reduces_bd_to_beta_reduces`.
    pub(super) fn add_beta_bd_embedding(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            &Self::beta_bd_embedding_src(),
            "beta_reduces_bd_to_beta_reduces: the iota-free step relation embeds in the full \
             one. beta_reduces_bd IS beta_reduces with the iota constructor dropped (14 arms vs \
             15), so this is a constructor-for-constructor transcription with the recursor's IH \
             threaded through each recursive arm — no content beyond the embedding. First named \
             sub-goal of link 4 of the def-eq completeness chain: bounding the algorithm's \
             whnf_red_step by the whnf_step relation that the `below` order descends on. It does \
             NOT establish that containment — whnf_red_step's app_left arm needs spine reasoning \
             about delta_reduct and is not touched here. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The embedding term. Split out so the shape tests below can check arm
    /// count and paren balance in milliseconds rather than in a ~40-minute
    /// spec build — these are source strings the Rust compiler never sees.
    fn beta_bd_embedding_src() -> String {
        let mut minors = String::new();
        for (name, binders, ih_pair, args) in BD_ARMS {
            let ih = if ih_pair.is_empty() {
                String::new()
            } else {
                format!("(_ : beta_reduces_bd {ih_pair}) (ih : beta_reduces {ih_pair}) ")
            };
            minors.push_str(&format!(
                "(fun {binders} {ih}=> beta_reduces.{name} {args}) "
            ));
        }
        format!(
            "def beta_reduces_bd_to_beta_reduces (e : KExpr) (e2 : KExpr) \
             (h : beta_reduces_bd e e2) : beta_reduces e e2 := \
             beta_reduces_bd.rec \
             (fun (x : KExpr) (y : KExpr) (_ : beta_reduces_bd x y) => beta_reduces x y) \
             {minors}e e2 h"
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_beta_bd_embedding_src_parens_balanced() {
        let src = Specification::beta_bd_embedding_src();
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0, "term must be paren-balanced");
    }

    /// Exactly fourteen minor premises — one per `beta_reduces_bd` constructor.
    /// Fifteen would mean the `iota` arm was wrongly included (it does not exist
    /// on the `bd` side); thirteen would mean one was dropped.
    #[test]
    fn test_beta_bd_embedding_src_has_fourteen_arms() {
        let src = Specification::beta_bd_embedding_src();
        let arms = src.matches("=> beta_reduces.").count();
        assert_eq!(
            arms, 14,
            "beta_reduces_bd has 14 constructors (beta_reduces' 15 minus iota), got {arms} arms"
        );
    }

    /// Every arm must target the *identically named* `beta_reduces`
    /// constructor. A transposition here — `pi_dom` mapped to `pi_cod`, say —
    /// still typechecks in some cases and would silently prove the wrong thing.
    #[test]
    fn test_beta_bd_embedding_arms_target_matching_constructors() {
        let src = Specification::beta_bd_embedding_src();
        for (name, _, _, _) in BD_ARMS {
            assert!(
                src.contains(&format!("=> beta_reduces.{name} ")),
                "arm `{name}` must map to the identically named beta_reduces constructor"
            );
        }
    }

    /// The `bd` relation has no `iota` constructor, so no arm may mention it.
    #[test]
    fn test_beta_bd_embedding_has_no_iota_arm() {
        let src = Specification::beta_bd_embedding_src();
        assert!(
            !src.contains("beta_reduces.iota"),
            "beta_reduces_bd is iota-free; an iota arm would not correspond to any constructor"
        );
    }

    /// Non-recursive arms (`beta`, `zeta`) must NOT bind an induction
    /// hypothesis, and recursive ones must. Getting this wrong shifts every
    /// subsequent minor premise.
    #[test]
    fn test_beta_bd_embedding_ih_binders_match_recursive_arms() {
        let src = Specification::beta_bd_embedding_src();
        let ih_count = src.matches("(ih : beta_reduces ").count();
        assert_eq!(
            ih_count, 12,
            "12 of the 14 arms are recursive (all but beta and zeta), got {ih_count} IH binders"
        );
    }
}
