//! Only checked ordinary helpers cross the unchanged reserved-name boundary.
use super::*;
use crate::term::TermKind;
use crate::validate::Env;
const INPUT: &str = include_str!("../../tests/fixtures/derived-diamond.ndjson");

#[test]
fn transparent_helpers_keep_a_named_checked_forwarding_definition() {
    let state = replay_state(INPUT.as_bytes(), Dialect::Lean4Export31).unwrap();
    assert_eq!(state.report.counts(), (73, BTreeMap::new()));
    for (original, alias) in &state.checked_aliases {
        let forward = state.env.const_def(alias).unwrap();
        assert_eq!(forward.transparency, Transparency::Transparent);
        let TermKind::Const(reference) = forward.body.kind() else {
            panic!("a checked helper must retain its named body");
        };
        assert_eq!(reference.name(), original);
        assert_eq!(
            state.env.num_level_params(alias),
            state.env.num_level_params(original)
        );
        assert_eq!(
            state.env.delta_priority(alias),
            state.env.delta_priority(original)
        );
        assert!(state.env.hidden_from_export(alias));
        assert!(!state.env.is_recursor(alias));
        assert!(!state.env.is_recursor(original));
    }
    assert!(state
        .checked_aliases
        .contains_key(&Name::from_dotted("ck0SharedDefDiamond.f24.casesOn")));
}

#[test]
fn an_ill_typed_ordinary_helper_gets_neither_a_declaration_nor_an_alias() {
    let original = Name::from_dotted("ck0SharedDefDiamond.f0.casesOn");
    let mut tables = Tables::new();
    let mut changed = false;
    let forged = INPUT
        .lines()
        .map(|line| {
            let mut value: Value = serde_json::from_str(line).unwrap();
            if value.get("in").is_some() || value.get("il").is_some() || value.get("ie").is_some() {
                tables.bind(&value).unwrap();
            }
            let forges_original = value.get("def").is_some_and(|decl| {
                tables.name(decl["name"].as_u64().unwrap()).unwrap() == original
            });
            if forges_original {
                value["def"]["value"] = value["def"]["type"].clone();
                changed = true;
            }
            serde_json::to_string(&value).unwrap() + "\n"
        })
        .collect::<String>();
    assert!(changed);
    let state = replay_state(forged.as_bytes(), Dialect::Lean4Export31).unwrap();
    let refused = state
        .report
        .rows
        .iter()
        .find(|row| row.name == original)
        .unwrap();
    assert_eq!(refused.verdict.as_ref().unwrap_err().reason(), "type-check");
    assert!(!state.checked_aliases.contains_key(&original));
    assert!(state.env.num_level_params(&original).is_none());
}
