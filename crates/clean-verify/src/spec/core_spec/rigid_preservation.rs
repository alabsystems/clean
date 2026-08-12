// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rigid_app_head` is preserved by reduction — the payoff of the shape-only
//! weakening.
//!
//! ```text
//! rigid_app_head_preserved      : rigid_app_head e -> par_reduces_cd env e e2 -> rigid_app_head e2
//! rigid_app_head_star_preserved : … -> par_reduces_cd_star env e e2 -> rigid_app_head e2
//! ```
//!
//! This is the statement that is **false** for `whnf_stuck_head`
//! (`rigid_app_head.rs` documents the counterexample) and true here, because no
//! `rigid_app_head` arm constrains a subterm.
//!
//! ## How each of the eleven arms closes
//!
//! | arm | resolution |
//! |---|---|
//! | `refl` | the hypothesis is the conclusion |
//! | `beta` | the head would be a `lam`; `app_inv` then `not_lam` |
//! | `app` | `app_inv` feeds the induction hypothesis, then rebuild |
//! | `lam` | a `lam` is not rigid — `not_lam` |
//! | `pi`, `forall_` | rebuild directly; the `pi` arm has no premises, and `forall_` is a reducible alias for `pi` |
//! | `let_`, `let_cong` | a `let_` is not rigid — `not_let` |
//! | `iota`, `delta` | `rigid_app_{iota,delta}_immune` contradicts the step |
//! | `proj` | rebuild directly — **the arm takes any subject**, which is exactly why this works |
//!
//! The `pi` and `proj` arms are where the shape-only design pays: both rebuild
//! with no obligation about the reduced subterms. Under `whnf_stuck_head` the
//! `proj` case would have needed `is_whnf` of the *new* subject, which is the
//! thing that fails.
//!
//! One helper is introduced here for the two `let_` arms —
//! `rigid_app_head_not_let`, the same argument-from-an-absent-constructor as
//! `not_lam`.
//!
//! `DerivedProved` throughout, empty axiom closures.

use crate::spec::core_spec::kexpr_discr::CD_STRUCTURAL_ARMS;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The five `rigid_app_head` constructors, as `(payload binders, applied form,
/// recursive sub-head or None)` — mirrored from `rigid_app_head.rs` because the
/// `not_let` induction needs the same arm list.
const RIGID_ARMS: [(&str, &str, Option<&str>); 6] = [
    ("(n : Level)", "(KExpr.sort n)", None),
    (
        "(pty : KExpr) (pbody : KExpr)",
        "(KExpr.pi pty pbody)",
        None,
    ),
    ("(v : Nat)", "(KExpr.lit v)", None),
    ("(af : KExpr) (aa : KExpr)", "(KExpr.app af aa)", Some("af")),
    (
        "(s : Name) (i : Nat) (sub : KExpr)",
        "(KExpr.proj s i sub)",
        None,
    ),
    // Mirrors `rigid_app_head.rs`'s table, which this DUPLICATES. The two must
    // stay in lockstep: a constructor added there and missed here fails only at
    // the spec build, ~30 minutes later, with an arity mismatch that names the
    // consumer rather than the table.
    ("(i : Nat)", "(KExpr.bvar i)", None),
];

impl Specification {
    /// Preservation, single-step and multi-step.
    pub(super) fn add_rigid_preservation(&mut self) -> Result<(), SpecError> {
        self.add_rigid_not_let()?;
        self.add_rigid_preserved_step()?;
        self.add_rigid_preserved_star()?;
        Ok(())
    }

    /// A rigid head is never a `let_`.
    fn add_rigid_not_let(&mut self) -> Result<(), SpecError> {
        let motive_at = |v: &str| {
            format!(
                "forall (C : Type) (zty : KExpr) (zval : KExpr) (zbody : KExpr), \
                 Eq KExpr {v} (KExpr.let_ zty zval zbody) -> C"
            )
        };
        let mut arms = String::new();
        for (payload, form, sub) in RIGID_ARMS {
            let extra = match sub {
                Some(v) => format!(
                    "(_hr : rigid_app_head {v}) (_ih : {ih}) ",
                    ih = motive_at(v)
                ),
                None => String::new(),
            };
            arms.push_str(&format!(
                "(fun {payload} {extra}(C : Type) (zty : KExpr) (zval : KExpr) (zbody : KExpr) \
                 (heq : Eq KExpr {form} (KExpr.let_ zty zval zbody)) => \
                 kexpr_discr_t C {form} (KExpr.let_ zty zval zbody) heq \
                 (Eq.refl Bool Bool.false)) "
            ));
        }
        self.add_recursive_def(
            &format!(
                "def rigid_app_head_not_let (x : KExpr) (hr : rigid_app_head x) : {motive} := \
                 rigid_app_head.rec (fun (z : KExpr) (_h : rigid_app_head z) => {m}) \
                 {arms}x hr",
                motive = motive_at("x"),
                m = motive_at("z"),
            ),
            "rigid_app_head_not_let: a rigid head is never a let_. The same \
             argument-from-an-absent-constructor as rigid_app_head_not_lam; needed by the two \
             let_ arms of the preservation induction, whose sources are let_ nodes. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The eleven minor premises of the preservation induction.
    fn rigid_preserved_arms() -> String {
        // Motive: rigid_app_head p -> rigid_app_head q. So each recursive
        // premise `par_reduces_cd env X Y` contributes the IH
        // `rigid_app_head X -> rigid_app_head Y`.
        let ih_ty = |from: &str, to: &str| format!("rigid_app_head {from} -> rigid_app_head {to}");
        // `names` gives a binder name per recursive premise; `_` elsewhere.
        let block = |idx: usize, proof_names: &[&str], ih_names: &[&str]| {
            let (payload, pairs, _src, _tgt) = CD_STRUCTURAL_ARMS[idx];
            let mut proofs = String::new();
            let mut ihs = String::new();
            for (slot, (from, to)) in pairs.iter().enumerate() {
                let pn = proof_names.get(slot).copied().unwrap_or("_");
                let inn = ih_names.get(slot).copied().unwrap_or("_");
                proofs.push_str(&format!("({pn} : par_reduces_cd env {from} {to}) "));
                ihs.push_str(&format!("({inn} : {}) ", ih_ty(from, to)));
            }
            (payload, proofs, ihs)
        };

        let mut arms = String::new();

        // refl
        arms.push_str("(fun (e0 : KExpr) (hr : rigid_app_head e0) => hr) ");

        // beta: the head is a lam, which is not rigid.
        {
            let (payload, proofs, ihs) = block(0, &[], &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[0];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(hr : rigid_app_head {src}) => \
                 rigid_app_head_not_lam (KExpr.lam bA bbody) \
                 (rigid_app_head_app_inv {src} hr (KExpr.lam bA bbody) barg \
                 (Eq.refl KExpr {src})) \
                 (rigid_app_head {tgt}) bA bbody (Eq.refl KExpr (KExpr.lam bA bbody))) "
            ));
        }

        // app: invert, feed the IH, rebuild.
        {
            let (payload, proofs, ihs) = block(1, &["hpf"], &["ihf"]);
            let (_, _, src, _tgt) = CD_STRUCTURAL_ARMS[1];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(hr : rigid_app_head {src}) => \
                 rigid_app_head.app af2 aa2 \
                 (ihf (rigid_app_head_app_inv {src} hr af aa (Eq.refl KExpr {src})))) "
            ));
        }

        // lam: not rigid.
        {
            let (payload, proofs, ihs) = block(2, &[], &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[2];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(hr : rigid_app_head {src}) => \
                 rigid_app_head_not_lam {src} hr (rigid_app_head {tgt}) lty lbody \
                 (Eq.refl KExpr {src})) "
            ));
        }

        // pi and forall_: rebuild directly. forall_ is a reducible alias for
        // pi, so both targets are pi nodes and the pi constructor serves.
        for (idx, dom2, body2) in [(3usize, "pdom2", "pbody2"), (4usize, "qdom2", "qbody2")] {
            let (payload, proofs, ihs) = block(idx, &[], &[]);
            let (_, _, src, _tgt) = CD_STRUCTURAL_ARMS[idx];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(_hr : rigid_app_head {src}) => \
                 rigid_app_head.pi {dom2} {body2}) "
            ));
        }

        // let_: not rigid.
        {
            let (payload, proofs, ihs) = block(5, &[], &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[5];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(hr : rigid_app_head {src}) => \
                 rigid_app_head_not_let {src} hr (rigid_app_head {tgt}) zty zval zbody \
                 (Eq.refl KExpr {src})) "
            ));
        }

        // iota / delta: immunity contradicts the step.
        for (ctor, envsel, immune, var) in [
            ("iota", "red_rec env", "rigid_app_iota_immune", "ie"),
            ("delta", "red_def env", "rigid_app_delta_immune", "de"),
        ] {
            arms.push_str(&format!(
                "(fun ({var} : KExpr) ({var}2 : KExpr) \
                 (hst : {ctor}_step ({envsel}) {var} {var}2) (hr : rigid_app_head {var}) => \
                 opt_none_ne_some_t KExpr {var}2 (rigid_app_head {var}2) \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
                 ({ctor}_reduct ({envsel}) {var}) (OptionType.some KExpr {var}2) \
                 (Eq.symm (OptionType KExpr) ({ctor}_reduct ({envsel}) {var}) \
                 (OptionType.none KExpr) ({immune} env {var} hr)) hst)) "
            ));
        }

        // let_cong: also a let_ source.
        {
            let (payload, proofs, ihs) = block(6, &[], &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[6];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(hr : rigid_app_head {src}) => \
                 rigid_app_head_not_let {src} hr (rigid_app_head {tgt}) cty cval cbody \
                 (Eq.refl KExpr {src})) "
            ));
        }

        // proj: rebuild with ANY subject — the shape-only payoff.
        {
            let (payload, proofs, ihs) = block(7, &[], &[]);
            let (_, _, src, _tgt) = CD_STRUCTURAL_ARMS[7];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(_hr : rigid_app_head {src}) => \
                 rigid_app_head.proj ps pi2 psub2) "
            ));
        }

        arms
    }

    fn add_rigid_preserved_step(&mut self) -> Result<(), SpecError> {
        let arms = Self::rigid_preserved_arms();
        self.add_recursive_def(
            &format!(
                "def rigid_app_head_preserved (env : RedEnv) (e : KExpr) (e2 : KExpr) \
                 (h : par_reduces_cd env e e2) : rigid_app_head e -> rigid_app_head e2 := \
                 par_reduces_cd.rec env \
                 (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd env p q) => \
                 rigid_app_head p -> rigid_app_head q) \
                 {arms}e e2 h"
            ),
            "rigid_app_head_preserved: THE PAYOFF — a rigid spine head stays rigid under one \
             parallel step. This is exactly the statement that is FALSE for whnf_stuck_head, and \
             true here because no rigid_app_head arm constrains a subterm. The pi and proj arms \
             are where the shape-only design earns itself: both rebuild with no obligation about \
             the reduced subterms, whereas under whnf_stuck_head the proj case would have needed \
             is_whnf of the NEW subject — the very thing that fails. beta and lam die by \
             not_lam, the two let_ arms by not_let, iota and delta by the immunity lemmas, and \
             the app arm inverts, feeds its induction hypothesis and rebuilds. DerivedProved, \
             zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_rigid_preserved_star(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def rigid_app_head_star_preserved (env : RedEnv) (e : KExpr) (e2 : KExpr) \
             (h : par_reduces_cd_star env e e2) : rigid_app_head e -> rigid_app_head e2 := \
             par_reduces_cd_star.rec env \
             (fun (p : KExpr) (q : KExpr) (_h : par_reduces_cd_star env p q) => \
             rigid_app_head p -> rigid_app_head q) \
             (fun (e0 : KExpr) (hr : rigid_app_head e0) => hr) \
             (fun (e0 : KExpr) (e1 : KExpr) (e3 : KExpr) \
             (hstep : par_reduces_cd env e0 e1) \
             (_hstar : par_reduces_cd_star env e1 e3) \
             (ih : rigid_app_head e1 -> rigid_app_head e3) \
             (hr : rigid_app_head e0) => \
             ih (rigid_app_head_preserved env e0 e1 hstep hr)) \
             e e2 h",
            "rigid_app_head_star_preserved: rigidity survives any number of parallel steps. Two \
             lines by induction on the closure once the single-step version exists — which is \
             the whole reason the shape-only predicate was introduced. This is what unblocks the \
             multi-step stuck-application inversion, and through it the head-tag preservation \
             the completeness capstone factors through. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rigid_preserved_arms_has_eleven_minor_premises() {
        let arms = Specification::rigid_preserved_arms();
        let minors = arms.matches("(fun ").count();
        assert_eq!(minors, 11, "expected 11 minor premises, got {minors}");
    }

    /// Declaration order, `iota`/`delta` at 8 and 9.
    #[test]
    fn test_rigid_preserved_arms_declaration_order() {
        let arms = Specification::rigid_preserved_arms();
        let landmarks = [
            "(fun (e0 : KExpr) (hr :",
            "rigid_app_head_not_lam (KExpr.lam bA bbody)",
            "rigid_app_head.app af2 aa2",
            "lty lbody",
            "rigid_app_head.pi pdom2 pbody2",
            "rigid_app_head.pi qdom2 qbody2",
            "zty zval zbody",
            "rigid_app_iota_immune",
            "rigid_app_delta_immune",
            "cty cval cbody",
            "rigid_app_head.proj ps pi2 psub2",
        ];
        let mut cursor = 0usize;
        for (position, mark) in landmarks.iter().enumerate() {
            let found = arms[cursor..].find(mark).unwrap_or_else(|| {
                panic!("minor premise {position} ({mark}) missing/out of order")
            });
            cursor += found + mark.len();
        }
    }

    /// Every recursive premise contributes a proof binder and an IH binder.
    #[test]
    fn test_rigid_preserved_arms_bind_proofs_and_ihs() {
        let arms = Specification::rigid_preserved_arms();
        let proofs = arms.matches(" : par_reduces_cd env ").count();
        let ihs = arms.matches(" : rigid_app_head ").count()
            - arms.matches("(hr : rigid_app_head ").count()
            - arms.matches("(_hr : rigid_app_head ").count();
        assert_eq!(
            proofs, 18,
            "18 recursive premises across the eight structural arms"
        );
        assert_eq!(
            ihs, 18,
            "one induction hypothesis per recursive premise (each `rigid_app_head X -> \
             rigid_app_head Y` contributes two mentions, minus the arm's own hr binder)"
        );
    }

    /// Free-variable check: every hypothesis-shaped identifier used must be
    /// bound in the same term. This is what caught the anonymous-binder bug in
    /// `stuck_app_rigidity`.
    #[test]
    fn test_rigid_preserved_arms_reference_only_bound_hypotheses() {
        let arms = Specification::rigid_preserved_arms();
        let chars: Vec<char> = arms.chars().collect();
        let mut bound: Vec<String> = Vec::new();
        for (idx, ch) in chars.iter().enumerate() {
            if *ch != '(' {
                continue;
            }
            let mut name = String::new();
            let mut cursor = idx + 1;
            while cursor < chars.len() && (chars[cursor].is_alphanumeric() || chars[cursor] == '_')
            {
                name.push(chars[cursor]);
                cursor += 1;
            }
            if !name.is_empty()
                && chars.get(cursor) == Some(&' ')
                && chars.get(cursor + 1) == Some(&':')
            {
                bound.push(name);
            }
        }
        let mut referenced: Vec<String> = Vec::new();
        let mut token = String::new();
        for ch in arms.chars() {
            if ch.is_alphanumeric() || ch == '_' || ch == '.' {
                token.push(ch);
            } else if !token.is_empty() {
                referenced.push(std::mem::take(&mut token));
            }
        }
        if !token.is_empty() {
            referenced.push(token);
        }
        for tok in referenced {
            let looks_local = tok.len() > 1
                && (tok.starts_with('h') || tok.starts_with("ih"))
                && tok
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
            if looks_local {
                assert!(
                    bound.contains(&tok),
                    "arm body references `{tok}`, which no binder in the same term introduces"
                );
            }
        }
    }

    /// The two arms that make the shape-only design worthwhile must rebuild
    /// unconditionally — no obligation about the reduced subterms.
    #[test]
    fn test_pi_and_proj_arms_rebuild_unconditionally() {
        let arms = Specification::rigid_preserved_arms();
        assert!(
            arms.contains(
                "(_hr : rigid_app_head (KExpr.proj ps pi2 psub)) => \
                           rigid_app_head.proj ps pi2 psub2"
            ),
            "the proj arm must rebuild at the REDUCED subject with no side obligation — this is \
             precisely what whnf_stuck_head could not do"
        );
        assert!(
            arms.contains("rigid_app_head.pi pdom2 pbody2"),
            "the pi arm must rebuild at the reduced components"
        );
    }

    #[test]
    fn test_rigid_preserved_arms_parens_balanced() {
        let arms = Specification::rigid_preserved_arms();
        let mut depth: i64 = 0;
        for ch in arms.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0);
    }
}
