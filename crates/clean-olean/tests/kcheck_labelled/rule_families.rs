// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Selected inventory rule families and their exact labelled checker steps.

use std::collections::BTreeMap;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{ConstantKind, Name, ReferenceKernel};
use serde::Deserialize;

use super::{is_type_mismatch, name, verdict_refl};

const CHECKER: &str = "KCheck.checker";
const CONTRACT_MODULE: &str = "KCheck.CheckerContracts";

struct RuleFamily {
    id: &'static str,
    constructor: &'static str,
    model_lemma: &'static str,
    model_contract: &'static str,
    step: &'static str,
    proof: &'static str,
    proof_module: &'static str,
    contract: &'static str,
    semantic_control: &'static str,
    equations: &'static [&'static str],
    ground_controls: &'static [(&'static str, &'static [&'static str])],
}

const RULE_FAMILIES: &[RuleFamily] = &[
    RuleFamily {
        id: "infer-sort",
        constructor: "CICL.CoreJudgmentIn.sort",
        model_lemma: "CICL.Model.CoreRules.sort",
        model_contract: "CICL.Model.Contracts.ruleSort",
        step: "KCheck.inferAnn",
        proof: "KCheck.inferAnn_sort_result",
        proof_module: "KCheck.InferAtoms",
        contract: "inferSortMeaning",
        semantic_control: "KCheck.Controls.infer_sort_contract",
        equations: &["inferSort_positive_fuel", "inferSort_zero_fuel"],
        ground_controls: &[
            ("inferSort_literal_accepted", &["forged_infer_sort_report"]),
            (
                "inferSort_literal_depth_refused",
                &["forged_infer_sort_accept_depth"],
            ),
        ],
    },
    RuleFamily {
        id: "infer-constant",
        constructor: "CICL.CoreJudgmentIn.constant",
        model_lemma: "CICL.Model.CoreRules.constant",
        model_contract: "CICL.Model.Contracts.ruleConstant",
        step: "KCheck.check",
        proof: "KCheck.check_const_result",
        proof_module: "KCheck.CheckAtoms",
        contract: "checkConstantMeaning",
        semantic_control: "KCheck.Controls.infer_constant_contract",
        equations: &[
            "checkConstant_found",
            "checkConstant_wrong_arity",
            "checkConstant_unknown",
        ],
        ground_controls: &[
            (
                "checkConstant_literal_accepted",
                &["forged_check_constant_type", "forged_check_constant_report"],
            ),
            (
                "checkConstant_literal_arity_refused",
                &["forged_check_constant_accept_arity"],
            ),
            (
                "checkConstant_literal_unknown_refused",
                &["forged_check_constant_unknown_arity"],
            ),
        ],
    },
    RuleFamily {
        id: "infer-let",
        constructor: "CICL.CoreJudgmentIn.letE",
        model_lemma: "CICL.Model.CoreRules.letE",
        model_contract: "CICL.Model.Contracts.ruleLetE",
        step: "KCheck.check",
        proof: "KCheck.check_let_composed",
        proof_module: "KCheck.CheckSound",
        contract: "checkLetMeaning",
        semantic_control: "KCheck.Controls.check_let_composed_contract",
        equations: &["checkLet_successor"],
        ground_controls: &[
            ("checkLet_literal_accepted", &["forged_check_let_type"]),
            (
                "checkLet_literal_open_refused",
                &["forged_check_let_accept_open"],
            ),
            (
                "checkLet_literal_type_refused",
                &["forged_check_let_accept_type"],
            ),
        ],
    },
    RuleFamily {
        id: "infer-lambda",
        constructor: "CICL.CoreJudgmentIn.lam",
        model_lemma: "CICL.Model.CoreRules.lam",
        model_contract: "CICL.Model.Contracts.ruleLam",
        step: "KCheck.check",
        proof: "KCheck.check_lam_composed",
        proof_module: "KCheck.CheckSound",
        contract: "checkLambdaMeaning",
        semantic_control: "KCheck.Controls.check_lam_composed_contract",
        equations: &["checkLambda_successor"],
        ground_controls: &[
            (
                "checkLambda_literal_accepted",
                &["forged_check_lambda_binder", "forged_check_lambda_report"],
            ),
            (
                "checkLambda_literal_open_refused",
                &["forged_check_lambda_accept_open"],
            ),
            (
                "checkLambda_literal_domain_refused",
                &["forged_check_lambda_accept_domain"],
            ),
        ],
    },
    RuleFamily {
        id: "infer-app",
        constructor: "CICL.CoreJudgmentIn.app",
        model_lemma: "CICL.Model.CoreRules.app",
        model_contract: "CICL.Model.Contracts.ruleApp",
        step: "KCheck.check",
        proof: "KCheck.check_app_composed",
        proof_module: "KCheck.CheckSound",
        contract: "checkAppMeaning",
        semantic_control: "KCheck.Controls.check_app_composed_contract",
        equations: &["checkApp_successor"],
        ground_controls: &[
            (
                "checkApp_literal_accepted",
                &["forged_check_app_unsubstituted", "forged_check_app_report"],
            ),
            (
                "checkApp_literal_non_pi_refused",
                &["forged_check_app_accept_non_pi"],
            ),
            (
                "checkApp_literal_conversion_refused",
                &["forged_check_app_accept_conversion"],
            ),
        ],
    },
    RuleFamily {
        id: "infer-pi",
        constructor: "CICL.CoreJudgmentIn.pi",
        model_lemma: "CICL.Model.CoreRules.pi",
        model_contract: "CICL.Model.Contracts.rulePi",
        step: "KCheck.check",
        proof: "KCheck.check_pi_composed",
        proof_module: "KCheck.CheckSound",
        contract: "checkPiMeaning",
        semantic_control: "KCheck.Controls.check_pi_composed_contract",
        equations: &["checkPi_successor"],
        ground_controls: &[
            (
                "checkPi_literal_accepted",
                &[
                    "forged_check_pi_binder",
                    "forged_check_pi_max",
                    "forged_check_pi_report",
                ],
            ),
            (
                "checkPi_literal_domain_refused",
                &["forged_check_pi_accept_domain"],
            ),
            (
                "checkPi_literal_codomain_refused",
                &["forged_check_pi_accept_codomain"],
            ),
        ],
    },
    RuleFamily {
        id: "infer-local-variable",
        constructor: "CICL.CoreJudgmentIn.bvar",
        model_lemma: "CICL.Model.LocalContextSemantics.inferFVar_sound",
        model_contract: "CICL.Model.Contracts.inferFVarSound",
        step: "KCheck.check",
        proof: "KCheck.check_bvar_result",
        proof_module: "KCheck.CheckAtoms",
        contract: "checkBVarMeaning",
        semantic_control: "KCheck.Controls.check_bvar_result_contract",
        equations: &[
            "checkBVar_successor",
            "checkBVar_literal_named_correspondence",
        ],
        ground_controls: &[
            (
                "checkBVar_literal_inner",
                &[
                    "forged_check_bvar_level",
                    "forged_check_bvar_type",
                    "forged_check_bvar_report",
                ],
            ),
            (
                "checkBVar_literal_outer",
                &["forged_check_bvar_outer_cursor"],
            ),
            (
                "checkBVar_literal_loose_refused",
                &["forged_check_bvar_accept_loose"],
            ),
            (
                "checkBVar_literal_free_refused",
                &["forged_check_bvar_accept_free"],
            ),
        ],
    },
    RuleFamily {
        id: "infer-mdata",
        constructor: "CICL.CoreJudgmentIn.mdata",
        model_lemma: "CICL.Model.CoreRules.mdata",
        model_contract: "CICL.Model.Contracts.ruleMdata",
        step: "KCheck.check",
        proof: "KCheck.check_mdata_result",
        proof_module: "KCheck.CheckSound",
        contract: "checkMdataMeaning",
        semantic_control: "KCheck.Controls.check_mdata_result_contract",
        equations: &["checkMdata_successor"],
        ground_controls: &[
            (
                "checkMdata_literal_accepted",
                &[
                    "forged_check_mdata_stale_cursor",
                    "forged_check_mdata_stale_report",
                ],
            ),
            (
                "checkMdata_literal_depth_refused",
                &["forged_check_mdata_accept_depth"],
            ),
            (
                "checkMdata_literal_free_refused",
                &["forged_check_mdata_accept_free"],
            ),
        ],
    },
];

#[derive(Deserialize)]
struct ModelBinding {
    family: String,
    constructor: String,
    lemma: String,
    contract: String,
}

pub(super) fn replay(
    raw_exports: &BTreeMap<Name, String>,
    loaded: &Environment,
    kernel: &mut ReferenceKernel,
) {
    let models: Vec<ModelBinding> = serde_json::from_str(include_str!(
        "../../../../data/cic_l_model_rule_bindings.json"
    ))
    .expect("model family bindings");
    for rule in RULE_FAMILIES {
        let mut matches = models.iter().filter(|binding| binding.family == rule.id);
        let model = matches
            .next()
            .unwrap_or_else(|| panic!("missing {} model binding", rule.id));
        assert!(
            matches.next().is_none(),
            "duplicate {} model binding",
            rule.id
        );
        assert_eq!(
            model.constructor, rule.constructor,
            "{} constructor",
            rule.id
        );
        assert_eq!(model.lemma, rule.model_lemma, "{} model lemma", rule.id);
        assert_eq!(
            model.contract, rule.model_contract,
            "{} model contract",
            rule.id
        );
        replay_rule(rule, raw_exports, loaded, kernel);
    }

    for rule in RULE_FAMILIES {
        let ground_equations = rule.ground_controls.len();
        let refused_mutations: usize = rule
            .ground_controls
            .iter()
            .map(|(_, forged)| forged.len())
            .sum();
        eprintln!(
            "checker-family-replay family={} constructor={} model_lemma={} model_contract={} checker={CHECKER} step={} semantic={} contract={CONTRACT_MODULE}.{} ground_equations={ground_equations} refused_mutations={refused_mutations}",
            rule.id, rule.constructor, rule.model_lemma, rule.model_contract, rule.step, rule.proof, rule.contract
        );
    }
}

fn replay_rule(
    rule: &RuleFamily,
    raw_exports: &BTreeMap<Name, String>,
    loaded: &Environment,
    kernel: &mut ReferenceKernel,
) {
    let admitted = kernel.environment();
    let check = |subject: Name, owner: &str, kind: ConstantKind| {
        assert_eq!(
            raw_exports.get(&subject).map(String::as_str),
            Some(owner),
            "raw owner for {subject}"
        );
        assert_eq!(
            loaded
                .get_constant_origin(&subject)
                .and_then(|origin| origin.module_name()),
            Some(owner),
            "loaded owner for {subject}"
        );
        let declaration = admitted
            .get_const(&subject)
            .expect("fenced checker rule declaration");
        assert_eq!(declaration.kind, kind, "wrong kind for {subject}");
        assert!(
            declaration.value.is_some()
                && !loaded.is_unsafe(&subject)
                && !loaded.is_partial(&subject),
            "{} requires a bodyful, safe and total declaration {subject}",
            rule.id
        );
    };
    check(name(CHECKER), "KCheck.Signature", ConstantKind::Definition);
    check(name(rule.step), "KCheck.Kernel", ConstantKind::Definition);
    check(name(rule.proof), rule.proof_module, ConstantKind::Theorem);
    check(
        contract_name(rule.contract),
        CONTRACT_MODULE,
        ConstantKind::Definition,
    );
    for &equation in rule.equations {
        check(
            contract_name(equation),
            CONTRACT_MODULE,
            ConstantKind::Theorem,
        );
    }
    for &(ground, forged) in rule.ground_controls {
        check(
            contract_name(ground),
            CONTRACT_MODULE,
            ConstantKind::Theorem,
        );
        for &mutation in forged {
            check(
                contract_name(mutation),
                CONTRACT_MODULE,
                ConstantKind::Definition,
            );
        }
    }

    let proof = loaded
        .get_const(&name(rule.proof))
        .expect("original checker proof");
    let contract = admitted
        .get_const(&contract_name(rule.contract))
        .expect("fenced checker rule contract");
    assert!(
        contract.type_.is_prop(),
        "checker rule contract must define a Prop"
    );
    let semantic = Declaration::Theorem {
        name: name(rule.semantic_control),
        level_params: proof.level_params.clone(),
        type_: contract
            .value
            .clone()
            .expect("expanded checker rule contract"),
        value: proof.value.clone().expect("original checker proof body"),
    };
    kernel
        .add_checked(semantic)
        .unwrap_or_else(|refusal| panic!("{} at {}: {refusal:?}", rule.proof, rule.contract));

    for &(ground, forged) in rule.ground_controls {
        replay_equations(kernel, ground, forged);
    }
}

fn replay_equations(kernel: &mut ReferenceKernel, ground: &str, forged: &[&str]) {
    let positive = kernel
        .environment()
        .get_const(&contract_name(ground))
        .expect("fenced ground checker theorem");
    let expected = positive.type_.clone();
    let good = Declaration::Theorem {
        name: name(&format!("KCheck.Controls.{ground}_evaluation")),
        level_params: positive.level_params.clone(),
        value: verdict_refl(&expected),
        type_: expected,
    };
    kernel
        .add_checked(good)
        .unwrap_or_else(|refusal| panic!("honest checker equation {ground}: {refusal:?}"));

    for &mutation in forged {
        let negative = kernel
            .environment()
            .get_const(&contract_name(mutation))
            .expect("fenced forged checker proposition");
        assert!(negative.type_.is_prop(), "{mutation} must define a Prop");
        let false_claim = negative.value.clone().expect("expanded forged proposition");
        let bad = Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{mutation}_evaluation")),
            level_params: negative.level_params.clone(),
            value: verdict_refl(&false_claim),
            type_: false_claim,
        };
        let outcome = kernel.add_checked(bad);
        assert!(
            is_type_mismatch(&outcome),
            "forged checker equation {mutation} must fail by type mismatch: {outcome:?}"
        );
    }
}

fn contract_name(label: &str) -> Name {
    name(&format!("{CONTRACT_MODULE}.{label}"))
}
