// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A matching head tag forces the head **shape**.
//!
//! For each of the six normal-form head shapes:
//!
//! ```text
//! nf_tag_forces_pi :
//!   nf_head x -> Eq Nat (kexpr_tag (pi pty pbody)) (kexpr_tag x) -> PiShape x
//! ```
//!
//! and likewise for `sort`, `lam`, `lit`, `app`, `proj`.
//!
//! ## Why six lemmas rather than one 36-arm grid
//!
//! With `nf_join_same_tag` in hand, the capstone knows the two normal forms
//! share a tag. Turning that into "and therefore the same shape, with these
//! components" is naturally a grid: six shapes on the left times six on the
//! right, thirty of them absurd. Written as one theorem that is a 36-arm term.
//!
//! Split by the left shape it becomes six independent lemmas of six arms each —
//! the same total work, but each one validates on its own. That matters
//! concretely here: a spec build costs ~21 minutes and reports **one** failing
//! declaration, so a 36-arm monolith that fails tells you far less per cycle
//! than six small ones.
//!
//! In each lemma exactly one arm builds a witness and the other five die by
//! `nat_discr_t`. Because `kexpr_tag` computes, those five are literally
//! `Eq.refl Bool Bool.false` — the mismatch is arithmetic, not an argument.
//!
//! ## Shape witnesses
//!
//! Six single-constructor inductives, one per shape, each packaging the
//! payload and the equation. The spec has no `Exists`, so this is the standard
//! idiom; and having them separate rather than as one sum type means the
//! capstone's case analysis is driven by which lemma it applied, not by a
//! second dispatch.
//!
//! `DerivedProved`, empty axiom closures; the witnesses are census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `(shape name, witness type, payload binders, applied form)`. The order is
/// irrelevant here — unlike the recursor tables, these are independent
/// declarations.
const SHAPES: [(&str, &str, &str, &str); 8] = [
    ("bvar", "BvarShape", "(bi : Nat)", "(KExpr.bvar bi)"),
    ("sort", "SortShape", "(n : Level)", "(KExpr.sort n)"),
    (
        "lam",
        "LamShape",
        "(lty : KExpr) (lbody : KExpr)",
        "(KExpr.lam lty lbody)",
    ),
    (
        "pi",
        "PiShape",
        "(pty : KExpr) (pbody : KExpr)",
        "(KExpr.pi pty pbody)",
    ),
    ("lit", "LitShape", "(v : Nat)", "(KExpr.lit v)"),
    (
        "app",
        "AppShape",
        "(af : KExpr) (aa : KExpr)",
        "(KExpr.app af aa)",
    ),
    (
        "proj",
        "ProjShape",
        "(ps : Name) (pidx : Nat) (psub : KExpr)",
        "(KExpr.proj ps pidx psub)",
    ),
    (
        "const",
        "ConstShape",
        "(cn : Name) (cus : ListType Level)",
        "(KExpr.const cn cus)",
    ),
];

/// The EIGHT leaves an `nf_head` case analysis produces, as
/// `(shape name, binders introduced, the term at that leaf, extra non-recursive
/// premise binders)`.
///
/// `nf_head` has four constructors — `lam`, `rigid`, `neutral`, `constdead` —
/// and the `rigid` arm fans out to `rigid_app_head`'s five in ITS declaration
/// order. So the leaf sequence is:
///
/// ```text
/// lam | rigid{sort, pi, lit, app, proj} | neutral | constdead
/// ```
///
/// Two leaves land on the same shape: `rigid/app` and `neutral` are both
/// applications. That is expected — a const-headed neutral and a
/// rigid-headed spine are different witnesses for the same head — and the
/// `app` lemma therefore builds its witness twice.
const NF_LEAVES: [(&str, &str, &str, &str); 9] = [
    (
        "lam",
        "(qty : KExpr) (qbody : KExpr)",
        "(KExpr.lam qty qbody)",
        "",
    ),
    ("sort", "(rn : Level)", "(KExpr.sort rn)", ""),
    (
        "pi",
        "(rpty : KExpr) (rpbody : KExpr)",
        "(KExpr.pi rpty rpbody)",
        "",
    ),
    ("lit", "(rv : Nat)", "(KExpr.lit rv)", ""),
    (
        "app",
        "(raf : KExpr) (raa : KExpr)",
        "(KExpr.app raf raa)",
        "",
    ),
    (
        "proj",
        "(rs : Name) (ri : Nat) (rsub : KExpr)",
        "(KExpr.proj rs ri rsub)",
        "",
    ),
    (
        "app",
        "(nf : KExpr) (na2 : KExpr)",
        "(KExpr.app nf na2)",
        "(_hin : iota_neutral nf) (_hii : iota_immune (KExpr.app nf na2)) ",
    ),
    (
        "const",
        "(cn : Name) (cus : ListType Level)",
        "(KExpr.const cn cus)",
        "(_hdd : Eq (OptionType KExpr) \
         (delta_reduct (red_def the_red_env) (KExpr.const cn cus)) (OptionType.none KExpr)) ",
    ),
    ("bvar", "(bi : Nat)", "(KExpr.bvar bi)", ""),
];

impl Specification {
    /// Shape witnesses and the six tag-forces-shape lemmas.
    pub(super) fn add_nf_shape(&mut self) -> Result<(), SpecError> {
        self.add_shape_witnesses()?;
        self.add_tag_forces_shape()?;
        Ok(())
    }

    fn add_shape_witnesses(&mut self) -> Result<(), SpecError> {
        for (name, witness, binders, form) in SHAPES {
            self.add_inductive(
                &format!(
                    "inductive {witness} (x : KExpr) : Type\n\
                     | mk : forall {binders}, Eq KExpr x {form} -> {witness} x"
                ),
                &format!(
                    "{witness} x: x IS a {name}, with its payload packaged. A \
                     single-constructor witness because the spec has no Exists. Kept separate \
                     from the other five rather than folded into a sum type, so that the \
                     completeness capstone's case analysis is driven by which lemma it applied \
                     rather than by a second dispatch. Census-neutral."
                ),
            )?;
        }
        Ok(())
    }

    /// One lemma per left-hand shape; each is a six-leaf case analysis on the
    /// right-hand term with five arms killed arithmetically.
    fn tag_forces_shape_src(target: usize) -> String {
        let (name, witness, binders, form) = SHAPES[target];
        let goal = |x: &str| format!("{witness} {x}");
        let hyp = |x: &str| format!("Eq Nat (kexpr_tag {form}) (kexpr_tag {x})");

        let leaf = |leaf_idx: usize| {
            let (leaf_name, leaf_binders, leaf_form, _extra) = NF_LEAVES[leaf_idx];
            if leaf_name == name {
                let args = leaf_binders
                    .split(") (")
                    .map(|b| {
                        b.trim_start_matches('(')
                            .trim_end_matches(')')
                            .split(" : ")
                            .next()
                            .unwrap_or("")
                            .to_string()
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("{witness}.mk {leaf_form} {args} (Eq.refl KExpr {leaf_form})")
            } else {
                format!(
                    "nat_discr_t ({g}) (kexpr_tag {form}) (kexpr_tag {leaf_form}) htag \
                     (Eq.refl Bool Bool.false)",
                    g = goal(leaf_form)
                )
            }
        };
        // A leaf's minor premise: payload binders, any extra non-recursive
        // premises, the recursive premise + IH where rigid_app_head recurses,
        // then the tag hypothesis.
        let arm = |leaf_idx: usize, recursive: bool| {
            let (_, leaf_binders, leaf_form, extra) = NF_LEAVES[leaf_idx];
            let rec_part = if recursive {
                format!(
                    "(_hraf : rigid_app_head raf) (_ihr : {h} -> {g}) ",
                    h = hyp("raf"),
                    g = goal("raf")
                )
            } else {
                String::new()
            };
            format!(
                "(fun {leaf_binders} {extra}{rec_part}(htag : {h}) => {body}) ",
                h = hyp(leaf_form),
                body = leaf(leaf_idx)
            )
        };

        let motive = format!("{h} -> {g}", h = hyp("z"), g = goal("z"));

        // rigid_app_head declaration order: sort, pi, lit, app, proj, bvar
        // => NF_LEAVES indices 1..=5 then 8, with index 4 (app) the recursive
        // one. The bvar leaf is REUSED from the nf_head arm rather than
        // duplicated: the two occurrences sit in different lambdas, so their
        // binders cannot collide.
        let mut rigid_arms = String::new();
        for leaf_idx in 1usize..=5 {
            rigid_arms.push_str(&arm(leaf_idx, leaf_idx == 4));
        }
        rigid_arms.push_str(&arm(8, false));

        format!(
            "def nf_tag_forces_{name} {binders} (x : KExpr) (hn : nf_head x) \
             (htag : {top_hyp}) : {top_goal} := \
             nf_head.rec (fun (z : KExpr) (_h : nf_head z) => {motive}) \
             {lam_arm}\
             (fun (e0 : KExpr) (hr : rigid_app_head e0) => \
             rigid_app_head.rec (fun (z : KExpr) (_h : rigid_app_head z) => {motive}) \
             {rigid_arms}e0 hr) \
             {neutral_arm}{const_arm}{bvar_arm}x hn htag",
            top_hyp = hyp("x"),
            top_goal = goal("x"),
            lam_arm = arm(0, false),
            neutral_arm = arm(6, false),
            const_arm = arm(7, false),
            bvar_arm = arm(8, false),
        )
    }

    fn add_tag_forces_shape(&mut self) -> Result<(), SpecError> {
        for (target, &(name, witness, _, _)) in SHAPES.iter().enumerate() {
            self.add_recursive_def(
                &Self::tag_forces_shape_src(target),
                &format!(
                    "nf_tag_forces_{name}: a normal-form head whose tag matches a {name}'s IS a \
                     {name}, payload and all ({witness}). Six leaves — nf_head's lam arm plus \
                     rigid_app_head's five — of which exactly one builds the witness and five die \
                     by nat_discr_t. Because kexpr_tag computes, those five mismatches are \
                     literally Eq.refl Bool Bool.false: a head disagreement is arithmetic here, \
                     not an argument. One of six sibling lemmas rather than a single 36-arm grid, \
                     because a spec build costs ~21 minutes and names ONE failing declaration, so \
                     six small theorems localise a failure where a monolith would not. \
                     DerivedProved, zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// EIGHT shapes, NINE leaves, and every leaf must name a real shape.
    /// Two leaves share the `app` shape — `rigid/app` and `neutral` — which is
    /// expected: a rigid-headed spine and a const-headed neutral are different
    /// witnesses for the same head. The counts moved when `nf_head` gained its
    /// `bvar` arm; the structural check below is the part with content, and it
    /// is what catches a leaf added without its shape witness.
    #[test]
    fn test_shape_tables_agree() {
        assert_eq!(SHAPES.len(), 8);
        assert_eq!(NF_LEAVES.len(), 9);
        let shape_names: Vec<&str> = SHAPES.iter().map(|(n, _, _, _)| *n).collect();
        for (n, _, _, _) in NF_LEAVES {
            assert!(
                shape_names.contains(&n),
                "nf_head leaf {n} has no corresponding shape witness"
            );
        }
        for n in &shape_names {
            assert!(
                NF_LEAVES.iter().any(|(ln, _, _, _)| ln == n),
                "shape {n} has no corresponding nf_head leaf"
            );
        }
        let app_leaves = NF_LEAVES.iter().filter(|(n, _, _, _)| *n == "app").count();
        assert_eq!(
            app_leaves, 2,
            "exactly two leaves are applications: rigid/app and neutral"
        );
    }

    /// Each lemma builds its witness once per EMITTED arm matching its shape and
    /// discriminates on every other.
    ///
    /// Emitted arms are NF_LEAVES plus one: since `rigid_app_head` gained a
    /// `bvar` constructor, the bvar leaf is emitted TWICE — once under
    /// `nf_head.bvar`, once under the rigid recursor. Both builds are correct;
    /// a bvar-headed term is now reachable by either route.
    #[test]
    fn test_each_lemma_builds_and_kills_exactly() {
        // The bvar leaf is the one emitted twice.
        let emitted = |name: &str| {
            NF_LEAVES.iter().filter(|(n, _, _, _)| *n == name).count() + usize::from(name == "bvar")
        };
        let total: usize = SHAPES.iter().map(|(n, _, _, _)| emitted(n)).sum();
        assert_eq!(
            total,
            NF_LEAVES.len() + 1,
            "every emitted arm must belong to exactly one shape"
        );
        for (target, &(name, witness, _, _)) in SHAPES.iter().enumerate() {
            let src = Specification::tag_forces_shape_src(target);
            let matching = emitted(name);
            let builds = src.matches(&format!("{witness}.mk ")).count();
            let kills = src.matches("nat_discr_t ").count();
            assert_eq!(
                builds, matching,
                "nf_tag_forces_{name}: one build per emitted arm ({matching}), found {builds}"
            );
            assert_eq!(
                kills,
                total - matching,
                "nf_tag_forces_{name}: every non-matching arm must be killed arithmetically"
            );
        }
    }

    /// `nf_head`'s four arms in declaration order, with the rigid fan-out in
    /// `rigid_app_head`'s own order. A transposition leaves every count correct.
    #[test]
    fn test_arm_order_follows_both_declarations() {
        let src = Specification::tag_forces_shape_src(0);
        let landmarks = [
            "(qty : KExpr)",  // nf_head.lam
            "(rn : Level)",   // rigid.sort
            "(rpty : KExpr)", // rigid.pi
            "(rv : Nat)",     // rigid.lit
            "(raf : KExpr)",  // rigid.app
            "(rs : Name)",    // rigid.proj
            "(nf : KExpr)",   // nf_head.neutral
            "(cn : Name)",    // nf_head.constdead
        ];
        let mut cursor = 0usize;
        for (position, mark) in landmarks.iter().enumerate() {
            let found = src[cursor..]
                .find(mark)
                .unwrap_or_else(|| panic!("leaf {position} ({mark}) missing or out of order"));
            cursor += found + mark.len();
        }
    }

    /// The two conditional arms must carry their obligations as BINDERS. If the
    /// neutral arm ever stopped binding iota_immune, the const case would look
    /// unconditional while resting on nothing.
    #[test]
    fn test_conditional_arms_bind_their_obligations() {
        for target in 0..SHAPES.len() {
            let src = Specification::tag_forces_shape_src(target);
            assert!(
                src.contains("(_hin : iota_neutral nf)")
                    && src.contains("(_hii : iota_immune (KExpr.app nf na2))"),
                "the neutral arm must bind BOTH iota obligations — a const-headed spine can \
                 iota-fire once its arguments become constructor-headed, so its tag stability \
                 is genuinely conditional"
            );
            assert!(
                src.contains("delta_reduct (red_def the_red_env) (KExpr.const cn cus)"),
                "the constdead arm must bind its delta-deadness obligation"
            );
        }
    }

    /// Only `rigid_app_head`'s `app` arm recurses.
    #[test]
    fn test_only_the_rigid_app_arm_binds_an_ih() {
        for target in 0..SHAPES.len() {
            let src = Specification::tag_forces_shape_src(target);
            assert_eq!(src.matches("(_ihr : ").count(), 1);
            assert_eq!(src.matches("(_hraf : rigid_app_head raf)").count(), 1);
        }
    }

    #[test]
    fn test_tag_forces_shape_srcs_parens_balanced() {
        for target in 0..SHAPES.len() {
            let src = Specification::tag_forces_shape_src(target);
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in shape {target}");
            }
            assert_eq!(depth, 0, "unbalanced parens in shape {target}");
        }
    }
}
