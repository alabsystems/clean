// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;

#[test]
fn string_numeric_name_components_and_environment_metadata_are_not_flattened() {
    let numeric = Name::anon().str("same").num(17);
    let string = Name::anon().str("same").str("17");
    assert_ne!(numeric, string);
    for n in [numeric, string, Name::anon(), name()] {
        let mut env = fixture(Expr::const_(n, vec![]));
        env.set_cumulative(true);
        env.set_option("codec-option".into(), Some("exact λ value".into()));
        env.set_lean4_core_strict_monads(true);
        let old = env.to_bincode().unwrap();
        let restored = Environment::from_dag_bincode(&env.to_dag_bincode().unwrap()).unwrap();
        assert_eq!(restored.to_bincode().unwrap(), old);
    }
}

#[test]
fn metadata_sequences_retain_duplicate_names_and_ordered_distinct_values() {
    let duplicate = name();
    let entries = vec![
        (duplicate.clone(), MDataValue::Bool(true)),
        (duplicate.clone(), MDataValue::Nat(17)),
        (duplicate, MDataValue::String("third value".into())),
    ];
    let mut reversed = entries.clone();
    reversed.reverse();
    let mut carriers = Vec::new();
    for expected in [entries, reversed] {
        let input = fixture(Expr::mdata(expected.clone(), Expr::bvar(0)));
        let bytes = input.to_dag_bincode().unwrap();
        let restored = Environment::from_dag_bincode(&bytes).unwrap();
        let ExprKind::MData(actual, inner) = value(&restored).kind() else {
            panic!("metadata node was dropped")
        };
        assert_eq!(actual, &expected);
        assert_eq!(actual.len(), 3);
        assert_eq!(inner.kind(), &ExprKind::BVar(0));
        assert_eq!(value(&input), value(&restored));
        carriers.push(bytes);
    }
    assert_ne!(
        carriers[0], carriers[1],
        "ordered metadata was silently sorted"
    );
}

#[test]
fn hash_map_insertion_and_random_hasher_order_do_not_choose_graph_ids() {
    let make = |reverse: bool| {
        let mut data: JsonEnvironment =
            serde_json::from_str(&fixture(Expr::bvar(0)).to_json().unwrap()).unwrap();
        data.constants = vec![
            ConstantInfo::new(
                Name::anon().str("z"),
                vec![],
                Expr::sort(Level::Zero),
                Some(Expr::nat_lit(19)),
                false,
            ),
            ConstantInfo::new(
                Name::anon().str("a"),
                vec![],
                Expr::sort(Level::Zero),
                Some(Expr::nat_lit(3)),
                false,
            ),
            ConstantInfo::new(
                Name::anon().num(17),
                vec![],
                Expr::sort(Level::Zero),
                Some(Expr::bvar(7)),
                false,
            ),
        ];
        if reverse {
            data.constants.reverse();
        }
        Environment::from_json(&serde_json::to_string(&data).unwrap()).unwrap()
    };
    let first = make(false).to_dag_bincode().unwrap();
    for reverse in [true, false, true, false] {
        let other = make(reverse).to_dag_bincode().unwrap();
        assert_eq!(
            first, other,
            "root traversal assigned IDs before ordering map keys"
        );
    }
}
