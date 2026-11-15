// Copyright 2026 Andrew Yates | Apache-2.0
//! Integration controls for an untrusted data codec, never proof authority.
use clean_kernel::env::{ConstantInfo, Declaration, JsonEnvironment};
use clean_kernel::expr::{BigNat, FVarId, MDataValue, Multiplicity, ZFCSetExpr};
use clean_kernel::tc::TypeChecker;
use clean_kernel::{with_decode_resource_limits, DecodeResourceLimits};
use clean_kernel::{BinderData, BinderInfo, Environment, Expr, ExprKind, Level, Name};
use serde::Serialize;
use std::collections::HashSet;
use std::sync::Arc;

#[path = "dag_environment_carrier/framing.rs"]
mod framing;
#[path = "dag_environment_carrier/metadata.rs"]
mod metadata;
use framing::{app, bvar, deep_name_const, encode, envelope, sort_zero, Envelope, Node};
fn flat_encode<T: Serialize>(value: &T) -> Vec<u8> {
    bincode::serde::encode_to_vec(value, bincode::config::standard()).unwrap()
}
fn name() -> Name {
    Name::anon().str("Codec.α").num(17).str("17")
}
fn fixture(expr: Expr) -> Environment {
    let data = JsonEnvironment {
        lean_level_profile: Default::default(),
        constants: vec![ConstantInfo::new(
            name(),
            vec![],
            Expr::sort(Level::zero()),
            Some(expr),
            false,
        )],
        constant_origins: vec![],
        inductives: vec![],
        constructors: vec![],
        recursors: vec![],
        quotients: vec![],
        structure_fields: vec![],
    };
    // Loading JSON is deliberately only untrusted carrier construction. This
    // is not add_decl, and these arbitrary syntax fixtures prove no theorem.
    Environment::from_json(&serde_json::to_string(&data).unwrap()).unwrap()
}
fn value(env: &Environment) -> &Expr {
    env.get_const(&name()).unwrap().value.as_ref().unwrap()
}
fn seed() -> Vec<u8> {
    fixture(Expr::bvar(0)).to_dag_bincode().unwrap()
}
fn clean_legacy() {
    let env = fixture(Expr::sort(Level::zero()));
    let bytes = env.to_bincode().unwrap();
    let restored = Environment::from_bincode(&bytes).unwrap();
    assert_eq!(restored.to_bincode().unwrap(), bytes);
    assert_eq!(flat_encode(&Expr::bvar(7)), vec![0, 7]);
}
fn declined(wire: &Envelope, needle: &str) {
    let err = Environment::from_dag_bincode(&encode(wire)).expect_err("malformed data accepted");
    assert!(err.to_string().contains(needle), "{err}");
    clean_legacy();
}

#[test]
fn every_current_core_and_extension_constructor_preserves_exact_fields() {
    let a = Arc::new(Expr::bvar(1));
    let b = Arc::new(Expr::bvar(2));
    let c = Arc::new(Expr::bvar(3));
    let d = Arc::new(Expr::bvar(4));
    let u = Level::param(Name::anon().str("u").num(31));
    let v = Level::param(Name::anon().num(19));
    let level = Level::IMax(
        Level::Succ(u.clone().into()).into(),
        Level::Max(u.clone().into(), v.clone().into()).into(),
    );
    let mut expressions = vec![
        Expr::bvar(42),
        Expr::from_kind(ExprKind::FVar(FVarId::new(43))),
        Expr::sort(level.clone()),
        Expr::const_(
            name(),
            vec![
                level,
                Level::zero(),
                Level::Succ(Level::zero().into()),
                Level::Max(u.clone().into(), v.clone().into()),
                Level::IMax(u.clone().into(), v.into()),
                u,
            ],
        ),
        Expr::from_kind(ExprKind::App(a.clone(), b.clone())),
        Expr::from_kind(ExprKind::Let(
            name(),
            a.clone(),
            b.clone(),
            c.clone(),
            false,
        )),
        Expr::from_kind(ExprKind::Let(name(), a.clone(), b.clone(), c.clone(), true)),
        Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(BigNat::Small(
            u64::MAX,
        )))),
        Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(BigNat::Big(
            vec![0, 1, u64::MAX],
        )))),
        Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::String(
            "\0λ/../payload".into(),
        ))),
        Expr::from_kind(ExprKind::Proj(name(), 9, a.clone())),
        Expr::from_kind(ExprKind::MData(
            vec![
                (Name::anon().str("bool"), MDataValue::Bool(true)),
                (Name::anon().num(7), MDataValue::Nat(u64::MAX)),
                (Name::anon().str("7"), MDataValue::String("meta λ".into())),
                (Name::anon().str("name"), MDataValue::Name(name())),
            ],
            a.clone(),
        )),
        Expr::from_kind(ExprKind::SProp),
        Expr::from_kind(ExprKind::Squash(a.clone())),
        Expr::from_kind(ExprKind::CubicalInterval),
        Expr::from_kind(ExprKind::CubicalI0),
        Expr::from_kind(ExprKind::CubicalI1),
        Expr::from_kind(ExprKind::CubicalPath {
            ty: a.clone(),
            left: b.clone(),
            right: c.clone(),
        }),
        Expr::from_kind(ExprKind::CubicalPathLam { body: a.clone() }),
        Expr::from_kind(ExprKind::CubicalPathApp {
            path: a.clone(),
            arg: b.clone(),
        }),
        Expr::from_kind(ExprKind::CubicalHComp {
            ty: a.clone(),
            phi: b.clone(),
            u: c.clone(),
            base: d.clone(),
        }),
        Expr::from_kind(ExprKind::CubicalTransp {
            ty: a.clone(),
            phi: b.clone(),
            base: c.clone(),
        }),
        Expr::from_kind(ExprKind::CubicalCoe {
            ty: a.clone(),
            r: b.clone(),
            s: c.clone(),
            base: d.clone(),
        }),
        Expr::from_kind(ExprKind::ZFCMem {
            element: a.clone(),
            set: b.clone(),
        }),
        Expr::from_kind(ExprKind::ZFCComprehension {
            domain: a.clone(),
            pred: b.clone(),
        }),
    ];
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        for mult in [Multiplicity::Zero, Multiplicity::One, Multiplicity::Many] {
            let data = BinderData::new(info, mult);
            expressions.push(Expr::from_kind(ExprKind::Lam(data, a.clone(), b.clone())));
            expressions.push(Expr::from_kind(ExprKind::Pi(data, a.clone(), b.clone())));
        }
    }
    for set in [
        ZFCSetExpr::Empty,
        ZFCSetExpr::Singleton(a.clone()),
        ZFCSetExpr::Pair(a.clone(), b.clone()),
        ZFCSetExpr::Union(a.clone()),
        ZFCSetExpr::PowerSet(a.clone()),
        ZFCSetExpr::Separation {
            set: a.clone(),
            pred: b.clone(),
        },
        ZFCSetExpr::Replacement {
            set: a.clone(),
            func: b.clone(),
        },
        ZFCSetExpr::Infinity,
        ZFCSetExpr::Choice(a),
    ] {
        expressions.push(Expr::from_kind(ExprKind::ZFCSet(set)));
    }
    let count = expressions.len();
    for expression in expressions {
        let env = fixture(expression);
        let legacy = env.to_bincode().unwrap();
        let bytes = env.to_dag_bincode().unwrap();
        let framed = envelope(&bytes);
        let root = &framed.nodes.last().unwrap().kind;
        // Ordinary flat serde remains an independent current-source tag
        // oracle; no scoped Expr-reference forwarding remains in it.
        assert_eq!(
            u32::from_le_bytes(root[..4].try_into().unwrap()),
            u32::from(flat_encode(value(&env).kind())[0])
        );
        if let ExprKind::ZFCSet(set) = value(&env).kind() {
            assert_eq!(
                u32::from_le_bytes(root[4..8].try_into().unwrap()),
                u32::from(flat_encode(set)[0])
            );
        }
        let restored = Environment::from_dag_bincode(&bytes).unwrap();
        assert_eq!(restored.get_const(&name()), env.get_const(&name()));
        assert_eq!(restored.to_bincode().unwrap(), legacy);
    }
    println!("constructor/field fixtures={count}; no declaration admission implied");
    clean_legacy();
}

fn diamond(depth: usize) -> Environment {
    let mut wire = envelope(&seed());
    wire.nodes = vec![Node {
        id: 0,
        kind: sort_zero(),
    }];
    for id in 2..depth as u32 + 2 {
        let kind = if id == 2 {
            bvar(0)
        } else {
            app(id - 1, id - 1)
        };
        wire.nodes.push(Node { id, kind });
    }
    wire.nodes.push(Node {
        id: 1,
        kind: app(depth as u32 + 1, depth as u32 + 1),
    });
    Environment::from_dag_bincode(&encode(&wire)).unwrap()
}
fn allocations(root: &Expr) -> usize {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(e) = pending.pop() {
        if !seen.insert(e as *const Expr) {
            continue;
        }
        if let ExprKind::App(f, a) = e.kind() {
            pending.push(f);
            pending.push(a);
        }
    }
    seen.len()
}
#[test]
fn exponentially_expanded_diamond_has_linear_carrier_and_restored_memory_shape() {
    let mut rows = vec![];
    for depth in [64usize, 256, 1024] {
        let env = diamond(depth);
        let before = allocations(value(&env));
        let bytes = env.to_dag_bincode().unwrap();
        let restored = Environment::from_dag_bincode(&bytes).unwrap();
        let after = allocations(value(&restored));
        assert_eq!(value(&env), value(&restored));
        assert!(
            bytes.len() < depth * 100 + 10_000,
            "nonlinear encoding: {}",
            bytes.len()
        );
        assert!(after <= depth + 4, "nonlinear allocation count: {after}");
        let ExprKind::App(left, right) = value(&restored).kind() else {
            panic!("missing diamond root")
        };
        assert!(
            Arc::ptr_eq(left, right),
            "the same DAG child reference was duplicated"
        );
        rows.push((depth, bytes.len(), before, after, Arc::ptr_eq(left, right)));
    }
    println!("(depth,bytes,input_allocations,restored_allocations,root_pointer_shared)={rows:?}");
}

#[test]
fn duplicate_cycle_forward_unknown_and_missing_root_references_decline() {
    let good = envelope(&seed());
    assert!(good.nodes.len() >= 2);
    let mut duplicate = good.clone();
    duplicate.nodes[1].id = duplicate.nodes[0].id;
    declined(&duplicate, "duplicate");
    for (kind, expected) in [
        (app(0, 0), "cyclic"),
        (app(1, 1), "forward"),
        (app(u32::MAX, u32::MAX), "unknown"),
    ] {
        let mut bad = good.clone();
        bad.nodes[0].kind = kind;
        declined(&bad, expected);
    }
    let mut root = good;
    root.nodes.pop();
    declined(&root, "unknown");
}

#[test]
fn format_trailing_truncation_and_inner_payload_trailing_bytes_decline() {
    let bytes = seed();
    let mut wrong = envelope(&bytes);
    wrong.magic[7] ^= 1;
    declined(&wrong, "format");
    for size in [0, 1, 7, bytes.len() / 2, bytes.len() - 1] {
        assert!(Environment::from_dag_bincode(&bytes[..size]).is_err());
        clean_legacy();
    }
    let mut outer = bytes.clone();
    outer.push(0);
    assert!(Environment::from_dag_bincode(&outer).is_err());
    let mut inner = envelope(&bytes);
    inner.nodes[0].kind.push(0);
    declined(&inner, "trailing");
    let mut env = envelope(&bytes);
    env.environment.push(0);
    declined(&env, "trailing");
}

#[test]
fn invalid_bvar_node_payload_and_aggregate_byte_limits_decline() {
    let mut bad = envelope(&seed());
    bad.nodes[0].kind = bvar(u32::MAX);
    declined(&bad, "bound variable");
    let mut payload = envelope(&seed());
    payload.nodes[0].kind = vec![0; 1024 * 1024 + 1];
    declined(&payload, "payload");
    let huge = vec![0; 256 * 1024 * 1024 + 1];
    assert!(Environment::from_dag_bincode(&huge)
        .expect_err("hostile carrier accepted")
        .to_string()
        .contains("byte limit"));
    clean_legacy();
}

#[test]
fn oversized_recursive_name_and_graph_depth_decline_and_reset_codec_scope() {
    let mut atom = envelope(&seed());
    atom.nodes[0].kind = deep_name_const(300);
    let encoded = encode(&atom);
    assert!(Environment::from_dag_bincode(&encoded)
        .expect_err("hostile carrier accepted")
        .to_string()
        .contains("budget"));
    clean_legacy();
    let mut wire = envelope(&seed());
    wire.nodes = vec![Node {
        id: 0,
        kind: sort_zero(),
    }];
    for id in 2..4100u32 {
        wire.nodes.push(Node {
            id,
            kind: if id == 2 {
                bvar(0)
            } else {
                app(id - 1, id - 1)
            },
        });
    }
    wire.nodes.push(Node {
        id: 1,
        kind: app(4099, 4099),
    });
    declined(&wire, "depth");
}

#[test]
fn encoding_error_restores_legacy_expr_behavior_and_next_codec_call() {
    let huge = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::String(
        "x".repeat(1024 * 1024 + 1).into(),
    )));
    assert!(fixture(huge)
        .to_dag_bincode()
        .expect_err("hostile carrier accepted")
        .to_string()
        .contains("payload"));
    clean_legacy();
    let good = seed();
    assert!(Environment::from_dag_bincode(&good).is_ok());
}

#[test]
fn outer_serde_budget_survives_nested_codec_and_unwinding() {
    let good = seed();
    with_decode_resource_limits(
        DecodeResourceLimits {
            max_nodes: 1,
            max_depth: 1,
        },
        || {
            Environment::from_dag_bincode(&good).unwrap();
            assert!(bincode::serde::decode_from_slice::<Expr, _>(
                &flat_encode(&Expr::sort(Level::zero())),
                bincode::config::standard()
            )
            .is_err());
        },
    );
    let panic = std::panic::catch_unwind(|| {
        with_decode_resource_limits(
            DecodeResourceLimits {
                max_nodes: 0,
                max_depth: 0,
            },
            || panic!("outer budget unwind control"),
        )
    });
    assert!(panic.is_err());
    clean_legacy();
    // The owned DAG decoder has independent local budgets and no serde
    // forwarding mode. This checks the unchanged outer serde budget API,
    // not a nonexistent DAG thread-local scope or native-memory guarantee.
}

#[test]
fn restored_environment_data_cannot_replace_fresh_kernel_admission() {
    let n = Name::anon().str("checkedCodecType");
    let decl = Declaration::Definition {
        name: n.clone(),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Expr::sort(Level::zero()),
        is_reducible: true,
    };
    let mut producer = Environment::default();
    producer.add_decl(decl).unwrap();
    let restored = Environment::from_dag_bincode(&producer.to_dag_bincode().unwrap()).unwrap();
    let info = restored.get_const(&n).unwrap();
    let mut fresh = Environment::default();
    fresh
        .add_decl(Declaration::Definition {
            name: n.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone().unwrap(),
            is_reducible: info.is_reducible,
        })
        .unwrap();
    TypeChecker::new(&fresh)
        .check_type(
            &Expr::const_(n, vec![]),
            &Expr::sort(Level::succ(Level::zero())),
        )
        .unwrap();
    let hostile = fixture(Expr::sort(Level::zero()));
    let hostile = Environment::from_dag_bincode(&hostile.to_dag_bincode().unwrap()).unwrap();
    let info = hostile.get_const(&name()).unwrap();
    let mut fresh = Environment::default();
    assert!(fresh
        .add_decl(Declaration::Definition {
            name: name(),
            level_params: vec![],
            type_: info.type_.clone(),
            value: info.value.clone().unwrap(),
            is_reducible: false
        })
        .is_err());
    assert!(TypeChecker::new(&fresh)
        .check_type(&Expr::const_(name(), vec![]), &info.type_)
        .is_err());
}

#[test]
fn excess_node_inventory_is_refused_before_any_expression_is_registered() {
    let wire = Envelope {
        magic: *b"CLENEDG2",
        environment: vec![],
        nodes: vec![
            Node {
                id: 0,
                kind: vec![]
            };
            1_000_001
        ],
    };
    declined(&wire, "node limit");
}
