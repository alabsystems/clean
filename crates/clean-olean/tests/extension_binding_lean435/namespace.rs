// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::{EnvExtensionEntry, EnvExtensionEntryData, MatcherInfo, TrustedEnvExt};
use clean_kernel::{BinderInfo, Declaration};

#[test]
fn persistent_matcher_namespace_confers_no_logical_constant_semantics() {
    let mut env = load();
    let key = n("Clean.matcherInfo.v1");
    env.add_decl(Declaration::Definition {
        name: key.clone(),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            c("Nat"),
            Expr::pi(BinderInfo::Default, c("Nat"), c("Nat")),
        ),
        value: Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(1)),
        ),
        is_reducible: false,
    })
    .unwrap();
    let info = MatcherInfo {
        num_params: 0,
        num_discrs: 0,
        alt_num_params: vec![0],
        u_elim_pos: None,
        discr_names: vec![],
        details: None,
    };
    env.register_matcher_info(key.clone(), info.clone())
        .unwrap();
    assert_eq!(env.get_matcher_info(&key), Some(&info));
    for invalidated in [false, true] {
        if invalidated {
            env.add_persistent_extension_entries(
                &key,
                0,
                vec![EnvExtensionEntry {
                    name: key.clone(),
                    data: EnvExtensionEntryData::Object(b"invalid metadata".to_vec()),
                }],
            );
            assert!(env.get_matcher_info(&key).is_none());
        }
        for input in [0, 1, 42] {
            let applied = Expr::apps(
                Expr::const_(key.clone(), vec![]),
                [Expr::nat_lit(input), Expr::nat_lit(99)],
            );
            assert!(production_equal(
                &env,
                &applied,
                &Expr::nat_lit(input),
                &c("Nat")
            ));
            assert!(production_comparison(
                &env,
                &applied,
                &Expr::nat_lit(99),
                &c("Nat"),
                false
            ));
        }
    }
    eprintln!("LEAN435_MATCHER_NAMESPACE: actual first-argument projection under the storage Name retains its own meaning with valid/conflicting metadata: PASS");
}
