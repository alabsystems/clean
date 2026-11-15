use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ProofFormula};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Function, FunctionSummary, Module};

#[test]
fn v41_clause_bindings_round_trip_including_recursive_datatype() {
    let mut m = Module::new("bindings");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    // A Datatype sort with a BY-NAME recursive reference (empty constructors),
    // nested inside an Array key — every string here must be interned by the
    // collection walk or the WRITER panics by name (`id_of`), before any bytes
    // exist for a decoder to read.
    let list = ClauseSort::Datatype {
        name: "List".into(),
        constructors: vec![
            ("nil".into(), vec![]),
            (
                "cons".into(),
                vec![
                    ("head".into(), ClauseSort::BitVec(64)),
                    (
                        "tail".into(),
                        ClauseSort::Datatype {
                            name: "List".into(),
                            constructors: vec![],
                        },
                    ),
                ],
            ),
        ],
    };
    let clause = ProofFormula {
        schema: "trust-types.Formula@1".into(),
        payload: "{}".into(),
        smtlib: None,
        sort: None,
        bindings: vec![
            (
                "x".into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(64),
                    place: ClausePlace::Param { index: 0 },
                },
            ),
            (
                "result".into(),
                ClauseBinding {
                    sort: ClauseSort::Bool,
                    place: ClausePlace::ResultSlot { index: 0 },
                },
            ),
            (
                "x_out".into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(64),
                    place: ClausePlace::MutParamExit { index: 0 },
                },
            ),
            (
                "w".into(),
                ClauseBinding {
                    sort: ClauseSort::RoundingMode,
                    place: ClausePlace::World,
                },
            ),
            (
                "u".into(),
                ClauseBinding {
                    sort: ClauseSort::Float { eb: 11, sb: 53 },
                    place: ClausePlace::Unwind,
                },
            ),
            (
                "v".into(),
                ClauseBinding {
                    sort: ClauseSort::Array(Box::new(list.clone()), Box::new(ClauseSort::Int)),
                    place: ClausePlace::Value(ValueId::new(0)),
                },
            ),
        ],
    };
    let summary = FunctionSummary::new()
        .with_params(vec!["x".into()])
        .ensuring(clause);
    let f = Function::declaration(FuncId::new(0), "f", ft, summary);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    let bytes = serialize_module(&m).expect("serialize_module: test fixture");
    let back = deserialize_module(&bytes).expect("decode: every clause string must be pooled");
    assert_eq!(
        back, m,
        "clause bindings must survive the binary round-trip"
    );

    let j = serde_json::to_string(&m).unwrap();
    assert_eq!(serde_json::from_str::<Module>(&j).unwrap(), m, "json");
    let mp = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(
        rmp_serde::from_slice::<Module>(&mp).unwrap(),
        m,
        "positional msgpack"
    );
    let _ = FuncTyId::new(0);
    let _ = BlockId::new(0);
}

/// The SAME clause carried on a module-level `ProofObligation`, which used to
/// go through an INLINE DUPLICATE of the formula encoding. That copy silently
/// dropped `bindings`, so this asserts the two paths agree.
#[test]
fn v41_clause_bindings_survive_on_a_proof_obligation_too() {
    use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
    use trust_ir::value::ProofId;

    let mut m = Module::new("obligation_bindings");
    let mut o = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Precondition,
        ProofStatus::Pending,
        "x fits in 64 bits",
    );
    o.formula = Some(ProofFormula {
        schema: "trust-types.Formula@1".into(),
        payload: "{}".into(),
        smtlib: None,
        sort: None,
        bindings: vec![(
            "x".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(64),
                place: ClausePlace::Param { index: 0 },
            },
        )],
    });
    m.proof_obligations.push(o);

    let back = deserialize_module(&serialize_module(&m).expect("serialize_module: test fixture"))
        .expect("decode");
    assert_eq!(
        back.proof_obligations[0]
            .formula
            .as_ref()
            .expect("formula")
            .bindings
            .len(),
        1,
        "an obligation formula must carry its bindings, like a summary clause does"
    );
    assert_eq!(back, m);
}
