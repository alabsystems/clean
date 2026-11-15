// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guarded dead-head suppliers. Unlike the older raw-absence interface, these
//! keep the head's universe arguments and cover stuck wrong-arity definitions.

use super::super::iota_immunity::ARM_ORDER;
use super::super::kexpr_discr::CD_STRUCTURAL_ARMS;

const DEAD: &str =
    "Eq (OptionType KExpr) (kdef_value_at (red_def env) nm us) (OptionType.none KExpr)";
const NO_REC: &str =
    "Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) (OptionType.none RecMeta)";

fn head(e: &str) -> String {
    format!("Eq KExpr (kapp_fn {e}) (KExpr.const nm us)")
}

fn lifted(e: &str) -> String {
    format!("LiftP ({})", head(e))
}

fn name_eq(e: &str, proof: &str) -> String {
    format!("Eq.cong KExpr (OptionType Name) kexpr_const_name (kapp_fn {e}) (KExpr.const nm us) {proof}")
}

fn unlift(e: &str, value: &str) -> String {
    let p = head(e);
    format!("LiftP.rec ({p}) (fun (_ : LiftP ({p})) => {p}) (fun (hp : {p}) => hp) ({value})")
}

fn step_source() -> String {
    let mut arms = String::new();
    for (slot, entry) in ARM_ORDER.iter().enumerate() {
        let arm = if let Some(index) = entry {
            let (payload, pairs, src, tgt) = CD_STRUCTURAL_ARMS[*index];
            let mut premises = String::new();
            let mut ihs = String::new();
            for (i, (from, to)) in pairs.iter().enumerate() {
                premises.push_str(&format!("(_hp{i} : par_reduces_cd env {from} {to}) "));
                ihs.push_str(&format!("(ih{i} : {} -> {}) ", head(from), lifted(to)));
            }
            let body = if *index == 1 {
                "ih0 hr".to_string()
            } else {
                format!(
                    "option_none_ne_some_type Name nm ({}) ({})",
                    lifted(tgt),
                    name_eq(src, "hr")
                )
            };
            format!(
                "(fun {payload} {premises}{ihs}(hr : {}) => {body})",
                head(src)
            )
        } else if slot == 0 {
            format!(
                "(fun (re : KExpr) (hr : {}) => LiftP.up ({}) hr)",
                head("re"),
                head("re")
            )
        } else if slot == 7 {
            format!("(fun (ie : KExpr) (ie2 : KExpr) (hi : iota_step (red_rec env) ie ie2) (hr : {}) => iota_step_no_recmeta_absurd (red_rec env) ie ie2 nm ({}) ({}) hrec hi)", head("ie"), lifted("ie2"), name_eq("ie", "hr"))
        } else {
            debug_assert_eq!(slot, 8);
            let lookup = "Eq.subst KExpr (fun (z : KExpr) => Eq (OptionType KExpr) (kdef_value_at (red_def env) nm (kexpr_const_levels z)) (OptionType.none KExpr)) (KExpr.const nm us) (kapp_fn de) (Eq.symm KExpr (kapp_fn de) (KExpr.const nm us) hr) hdef";
            let none = format!(
                "delta_reduct_no_value_at (red_def env) de nm ({}) ({lookup})",
                name_eq("de", "hr")
            );
            format!("(fun (de : KExpr) (de2 : KExpr) (hd : delta_step (red_def env) de de2) (hr : {}) => option_none_ne_some_type KExpr de2 ({}) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def env) de) (OptionType.some KExpr de2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def env) de) (OptionType.none KExpr) ({none})) hd))", head("de"), lifted("de2"))
        };
        arms.push_str(&arm);
        arms.push(' ');
    }
    let rec = format!("par_reduces_cd.rec env (fun (p : KExpr) (q : KExpr) (_ : par_reduces_cd env p q) => {} -> {}) {arms} e e2 h hh", head("p"), lifted("q"));
    format!("def const_head_levels_preserved_cd (env : RedEnv) (nm : Name) (us : ListType Level) (hdef : {DEAD}) (hrec : {NO_REC}) (e : KExpr) (e2 : KExpr) (h : par_reduces_cd env e e2) (hh : {}) : {} := {}", head("e"), head("e2"), unlift("e2", &rec))
}

fn star_source() -> String {
    let rec = format!("par_reduces_cd_star.rec env (fun (p : KExpr) (q : KExpr) (_ : par_reduces_cd_star env p q) => {} -> {}) (fun (re : KExpr) (hr : {}) => LiftP.up ({}) hr) (fun (sx : KExpr) (sy : KExpr) (sz : KExpr) (hs : par_reduces_cd env sx sy) (_ht : par_reduces_cd_star env sy sz) (ih : {} -> {}) (hr : {}) => ih (const_head_levels_preserved_cd env nm us hdef hrec sx sy hs hr)) e e2 h hh", head("p"), lifted("q"), head("re"), head("re"), head("sy"), lifted("sz"), head("sx"));
    format!("def const_head_levels_star_preserved (env : RedEnv) (nm : Name) (us : ListType Level) (hdef : {DEAD}) (hrec : {NO_REC}) (e : KExpr) (e2 : KExpr) (h : par_reduces_cd_star env e e2) (hh : {}) : {} := {}", head("e"), head("e2"), unlift("e2", &rec))
}

fn neutral_source() -> String {
    let forms: [(&str, &[&str], &str); 9] = [
        ("(sl : Level)", &[], "(KExpr.sort sl)"),
        ("(bi : Nat)", &[], "(KExpr.bvar bi)"),
        (
            "(af : KExpr) (aa : KExpr)",
            &["af", "aa"],
            "(KExpr.app af aa)",
        ),
        (
            "(lt : KExpr) (lb : KExpr)",
            &["lt", "lb"],
            "(KExpr.lam lt lb)",
        ),
        (
            "(pt : KExpr) (pb : KExpr)",
            &["pt", "pb"],
            "(KExpr.pi pt pb)",
        ),
        (
            "(cn : Name) (cus : ListType Level)",
            &[],
            "(KExpr.const cn cus)",
        ),
        (
            "(zt : KExpr) (zv : KExpr) (zb : KExpr)",
            &["zt", "zv", "zb"],
            "(KExpr.let_ zt zv zb)",
        ),
        (
            "(sn : Name) (idx : Nat) (sub : KExpr)",
            &["sub"],
            "(KExpr.proj sn idx sub)",
        ),
        ("(lit : Nat)", &[], "(KExpr.lit lit)"),
    ];
    let mut arms = String::new();
    for (index, (payload, children, form)) in forms.iter().enumerate() {
        let ihs = children
            .iter()
            .enumerate()
            .map(|(i, e)| format!("(ih{i} : {} -> iota_neutral {e})", head(e)))
            .collect::<Vec<_>>()
            .join(" ");
        let body = if index == 2 {
            "iota_neutral.app af aa (ih0 hh) (iota_immune_of_guarded_dead_head nm us hdef hrec (KExpr.app af aa) hh)".to_string()
        } else if index == 5 {
            let dead = "delta_reduct_no_value_at (red_def the_red_env) (KExpr.const nm us) nm (Eq.refl (OptionType Name) (OptionType.some Name nm)) hdef";
            format!("Eq.substType KExpr (fun (z : KExpr) => iota_neutral z) (KExpr.const nm us) {form} (Eq.symm KExpr {form} (KExpr.const nm us) hh) (iota_neutral.const nm us ({dead}) ({dead}))")
        } else {
            format!(
                "option_none_ne_some_type Name nm (iota_neutral {form}) ({})",
                name_eq(form, "hh")
            )
        };
        arms.push_str(&format!(
            "(fun {payload} {ihs} (hh : {}) => {body}) ",
            head(form)
        ));
    }
    format!("def iota_neutral_of_guarded_dead_head (nm : Name) (us : ListType Level) (hdef : {}) (hrec : {}) (e : KExpr) : {} -> iota_neutral e := KExpr.rec (fun (z : KExpr) => {} -> iota_neutral z) {arms} e", DEAD.replace(" env)", " the_red_env)"), NO_REC.replace(" env)", " the_red_env)"), head("e"), head("z"))
}

pub(super) fn declarations() -> Vec<String> {
    let dead = DEAD.replace(" env)", " the_red_env)");
    let no_rec = NO_REC.replace(" env)", " the_red_env)");
    let preserved = "const_head_levels_star_preserved the_red_env nm us hdef hrec e e2 hstar hh";
    vec![
        step_source(),
        star_source(),
        format!("def iota_immune_of_guarded_dead_head (nm : Name) (us : ListType Level) (hdef : {dead}) (hrec : {no_rec}) (e : KExpr) (hh : {}) : iota_immune e := fun (e2 : KExpr) (r : KExpr) (hstar : par_reduces_cd_star the_red_env e e2) (hfire : iota_step (red_rec the_red_env) e2 r) => iota_step_no_recmeta_absurd (red_rec the_red_env) e2 r nm Empty ({}) hrec hfire", head("e"), name_eq("e2", &format!("({preserved})"))),
        neutral_source(),
        format!("def nf_head_app_of_guarded_dead_head (nm : Name) (us : ListType Level) (hdef : {dead}) (hrec : {no_rec}) (f : KExpr) (a : KExpr) (hh : {}) : nf_head (KExpr.app f a) := nf_head.neutral f a (iota_neutral_of_guarded_dead_head nm us hdef hrec f hh) (iota_immune_of_guarded_dead_head nm us hdef hrec (KExpr.app f a) hh)", head("(KExpr.app f a)")),
        format!("def hnf3_app_residual_of_guarded_dead_head (r0 : KExpr) (k0 : Nat) (zf : KExpr) (za : KExpr) (nm : Name) (us : ListType Level) (hdef : {dead}) (hrec : {no_rec}) (hh : {}) (_hs : wh3_stuck_at k0 r0) (heq : Eq KExpr r0 (KExpr.app zf za)) : nf_head r0 := Eq.substType KExpr (fun (z : KExpr) => nf_head z) (KExpr.app zf za) r0 (Eq.symm KExpr r0 (KExpr.app zf za) heq) (nf_head_app_of_guarded_dead_head nm us hdef hrec zf za (Eq.subst KExpr (fun (z : KExpr) => {}) r0 (KExpr.app zf za) heq hh))", head("r0"), head("z")),
    ]
}

/// This semantic-name fixture is a stored monomorphic definition. Giving it
/// one universe argument demonstrates the new branch on the actual reflection,
/// not on an absent name or a hypothetical environment.
pub(super) fn witnesses() -> Vec<String> {
    let nm = "fixture_def_env_closed_b_name";
    let us = "(ListType.cons Level Level.zero (ListType.nil Level))";
    let f = format!("(KExpr.const {nm} {us})");
    let a = "(KExpr.sort Level.zero)";
    vec![
        format!("def guarded_head_wrong_arity_no_value : Eq (OptionType KExpr) (kdef_value_at (red_def the_red_env) {nm} {us}) (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)"),
        format!("def guarded_head_wrong_arity_raw_present : Eq Bool (opt_isnone KExpr (defval_for (red_def the_red_env) {nm})) Bool.false := Eq.refl Bool Bool.false"),
        format!("def guarded_head_wrong_arity_nf_head : nf_head (KExpr.app {f} {a}) := nf_head_app_of_guarded_dead_head {nm} {us} guarded_head_wrong_arity_no_value (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta)) {f} {a} (Eq.refl KExpr {f})"),
    ]
}

#[cfg(test)]
mod tests {
    #[test]
    fn guarded_head_sources_parse_and_do_not_assume_raw_absence() {
        let sources = super::declarations();
        assert_eq!(sources.len(), 6);
        for source in sources {
            crate::test_utils::parse_check(&source).expect("guarded head source parses");
            assert!(!source.contains("defval_for"));
            assert!(source.contains("kdef_value_at"));
            assert!(source.contains("KExpr.const nm us"));
        }
    }

    #[test]
    fn wrong_arity_witnesses_parse_and_use_the_semantic_definition_name() {
        let sources = super::witnesses();
        assert_eq!(sources.len(), 3);
        for source in &sources {
            crate::test_utils::parse_check(source).expect("wrong-arity witness parses");
            assert!(source.contains("fixture_def_env_closed_b_name"));
            assert!(!source.contains("kcre_name_"));
        }
        assert!(sources[0].contains("kdef_value_at"));
        assert!(sources[1].contains("opt_isnone KExpr (defval_for"));
        assert!(sources[2].contains("nf_head_app_of_guarded_dead_head"));
        assert!(sources[2].contains("guarded_head_wrong_arity_no_value"));
    }
}
