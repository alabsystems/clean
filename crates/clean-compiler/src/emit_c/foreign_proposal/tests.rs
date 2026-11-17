// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::lcnf::{ExternAttr, ExternEntry, Param};
use clean_kernel::{Expr, FVarId};

fn bridge(entries: &[(&str, &str)]) -> FfiBridge {
    let named: Vec<_> = entries
        .iter()
        .map(|(name, symbol)| (Name::from_string(name), *symbol))
        .collect();
    bridge_named(&named)
}
fn bridge_named(entries: &[(Name, &str)]) -> FfiBridge {
    let params = [
        Param::new(
            FVarId::new(0),
            Name::from_string("left"),
            Expr::const_str("UInt64"),
        ),
        Param::new(
            FVarId::new(1),
            Name::from_string("right"),
            Expr::const_str("UInt64"),
        ),
    ];
    let result = Expr::const_str("UInt64");
    let attrs: Vec<_> = entries
        .iter()
        .map(|(_, symbol)| ExternAttr {
            entries: vec![ExternEntry {
                backend: "c".into(),
                name: (*symbol).into(),
            }],
        })
        .collect();
    let rows: Vec<_> = entries
        .iter()
        .zip(&attrs)
        .map(|((name, _), attr)| (name.clone(), params.as_slice(), &result, attr))
        .collect();
    FfiBridge::from_lcnf_externs(&rows)
}

#[test]
fn test_only_selected_metadata_binds_the_actual_foreign_call() {
    let logical = Name::from_string("User.actualLogicalName");
    let bridge = bridge(&[
        ("User.actualLogicalName", "actual_c_symbol"),
        ("Catalog.only", "do_not_emit"),
    ]);
    let data = propose_boxed_foreign_c(&bridge, std::slice::from_ref(&logical)).unwrap();
    assert_eq!(data.entries.len(), 1);
    let entry = &data.entries[0];
    assert_eq!(entry.lean_name, logical);
    assert_eq!(entry.scalar_symbol, "actual_c_symbol");
    assert_eq!(entry.scalar_params, [IRType::UInt64, IRType::UInt64]);
    assert_eq!(entry.scalar_return, IRType::UInt64);
    assert!(data
        .code
        .contains("extern uint64_t actual_c_symbol(uint64_t, uint64_t);"));
    assert!(
        data.code.contains("actual_c_symbol(_x2, _x3)"),
        "{}",
        data.code
    );
    assert!(!data.code.contains("do_not_emit"));
    assert_ne!(entry.boxed_symbol, entry.scalar_symbol);
    let ordinary = crate::emit_c::emit_c(std::slice::from_ref(&entry.adapter)).unwrap();
    assert!(!ordinary.contains("actual_c_symbol"));
    assert!(
        ordinary.contains("l_User_actualLogicalName(_x2, _x3)"),
        "{ordinary}"
    );
}

#[test]
fn test_missing_ambiguous_or_repeated_identity_refuses() {
    let name = Name::from_string("User.fn");
    assert!(matches!(
        propose_boxed_foreign_c(
            &FfiBridge::from_lcnf_externs(&[]),
            std::slice::from_ref(&name)
        ),
        Err(ForeignCProposalError::MissingOrAmbiguous(_))
    ));
    let one = bridge(&[("User.fn", "c_one")]);
    assert!(matches!(
        propose_boxed_foreign_c(&one, &[name.clone(), name.clone()]),
        Err(ForeignCProposalError::Duplicate(_))
    ));
    let two = bridge(&[("User.fn", "c_one"), ("User.fn", "c_two")]);
    assert!(matches!(
        propose_boxed_foreign_c(&two, &[name]),
        Err(ForeignCProposalError::MissingOrAmbiguous(_))
    ));
}

#[test]
fn test_c_spelling_and_request_limits_are_only_producer_refusals() {
    let name = Name::from_string("User.fn");
    let invalid = bridge(&[("User.fn", "c_symbol(); injected()")]);
    assert!(matches!(
        propose_boxed_foreign_c(&invalid, std::slice::from_ref(&name)),
        Err(ForeignCProposalError::InvalidSymbol(_))
    ));
    assert!(matches!(
        propose_boxed_foreign_c(&invalid, &vec![name; 33]),
        Err(ForeignCProposalError::TooLarge)
    ));
}

#[test]
fn test_symbol_collision_scalar_equals_own_boxed_entry_refuses() {
    let name = Name::from_string("User.fn");
    let first = propose_boxed_foreign_c(
        &bridge(&[("User.fn", "c_one")]),
        std::slice::from_ref(&name),
    )
    .unwrap();
    let actual_boxed_symbol = &first.entries[0].boxed_symbol;
    let changed = bridge(&[("User.fn", actual_boxed_symbol)]);
    assert!(
        matches!(
            propose_boxed_foreign_c(&changed, &[name]),
            Err(ForeignCProposalError::SymbolCollision(_))
        ),
        "scalar symbol must not alias its boxed entry"
    );
}

#[test]
fn test_symbol_collision_scalar_equals_other_boxed_entry_refuses() {
    let left = Name::from_string("User.left");
    let right = Name::from_string("User.right");
    let first = propose_boxed_foreign_c(
        &bridge(&[("User.left", "c_left"), ("User.right", "c_right")]),
        &[left.clone(), right.clone()],
    )
    .unwrap();
    let actual_left_boxed = &first.entries[0].boxed_symbol;
    let changed = bridge(&[("User.left", "c_left"), ("User.right", actual_left_boxed)]);
    for requested in [[left.clone(), right.clone()], [right, left]] {
        assert!(
            matches!(
                propose_boxed_foreign_c(&changed, &requested),
                Err(ForeignCProposalError::SymbolCollision(_))
            ),
            "scalar symbol must not alias another boxed entry in either request order"
        );
    }
}

#[test]
fn test_distinct_structured_names_keep_distinct_boxed_entries() {
    let left = Name::anon();
    let right = Name::anon().str("");
    assert_ne!(left, right);
    let params = [(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)];
    let a = mk_boxed_version_from_signature(&left, &params, &IRType::UInt64);
    let b = mk_boxed_version_from_signature(&right, &params, &IRType::UInt64);
    // The existing mangler escapes the empty component. This is a positive
    // identity control, not a manufactured collision or a mangler change.
    assert_ne!(a.name, b.name);
    let meta = bridge_named(&[(left.clone(), "c_left"), (right.clone(), "c_right")]);
    let proposal = propose_boxed_foreign_c(&meta, &[left, right]).unwrap();
    assert_ne!(
        proposal.entries[0].boxed_symbol,
        proposal.entries[1].boxed_symbol
    );
}

fn incompatible_alias_bridge(return_type: bool) -> FfiBridge {
    let word = Expr::const_str("UInt64");
    let boolean = Expr::const_str("Bool");
    let params = [
        Param::new(FVarId::new(0), Name::from_string("left"), word.clone()),
        Param::new(FVarId::new(1), Name::from_string("right"), word.clone()),
    ];
    let attr = ExternAttr {
        entries: vec![ExternEntry {
            backend: "c".into(),
            name: "shared_c_symbol".into(),
        }],
    };
    FfiBridge::from_lcnf_externs(&[
        (Name::from_string("User.left"), &params, &word, &attr),
        (
            Name::from_string("User.right"),
            if return_type { &params } else { &params[..1] },
            if return_type { &boolean } else { &word },
            &attr,
        ),
    ])
}

#[test]
fn test_symbol_collision_incompatible_scalar_return_refuses() {
    assert!(
        matches!(
            propose_boxed_foreign_c(
                &incompatible_alias_bridge(true),
                &[
                    Name::from_string("User.left"),
                    Name::from_string("User.right")
                ]
            ),
            Err(ForeignCProposalError::IncompatibleAlias(_))
        ),
        "one C symbol cannot have incompatible result types"
    );
}
#[test]
fn test_symbol_collision_incompatible_scalar_parameters_refuses() {
    assert!(
        matches!(
            propose_boxed_foreign_c(
                &incompatible_alias_bridge(false),
                &[
                    Name::from_string("User.left"),
                    Name::from_string("User.right")
                ]
            ),
            Err(ForeignCProposalError::IncompatibleAlias(_))
        ),
        "one C symbol cannot have incompatible parameter lists"
    );
}
#[test]
fn test_identical_scalar_aliases_remain_proposal_data() {
    let data = propose_boxed_foreign_c(
        &bridge(&[
            ("User.left", "shared_c_symbol"),
            ("User.right", "shared_c_symbol"),
        ]),
        &[
            Name::from_string("User.left"),
            Name::from_string("User.right"),
        ],
    )
    .unwrap();
    assert_eq!(data.entries.len(), 2);
    assert_eq!(data.entries[0].scalar_symbol, data.entries[1].scalar_symbol);
    assert_ne!(data.entries[0].boxed_symbol, data.entries[1].boxed_symbol);
}
