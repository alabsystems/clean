//! Qualification utility linked to the exact native WP implementation under test.
//! It reconstructs the test mutation with the shared IR API, never interprets it.
use std::{env, fs};
use trust_ir::{Inst, InstrNode, Ty, ValueId};

fn main() {
    let path = env::args()
        .nth(1)
        .expect("one native two-cell envelope path");
    let capture: serde_json::Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    let bundle: trust_ir::NativeVerificationBundle =
        serde_json::from_value(capture["bundle"].clone()).unwrap();
    let original: trust_ir::NativeVerificationBundle =
        serde_json::from_str(capture["original_capture"].as_str().unwrap()).unwrap();
    assert_eq!(
        original.module.stable_digest(),
        original.trust_ir_module_digest
    );
    let original_bytes: Vec<u8> =
        serde_json::from_value(capture["derived_original_bytes"].clone()).unwrap();
    assert_eq!(
        trust_ir::binary::serialize_module(&original.module).unwrap(),
        original_bytes
    );
    let mut expected = original.module;
    let function = &mut expected.functions[0];
    function.blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Alloca {
            ty: Ty::Bool,
            count: None,
            align: None,
        })
        .with_result(ValueId::new(16)),
    );
    function.blocks[3].body.insert(
        0,
        InstrNode::new(Inst::Store {
            ty: Ty::Bool,
            ptr: ValueId::new(16),
            value: ValueId::new(5),
            volatile: false,
            align: None,
        }),
    );
    function.blocks[3].body.insert(
        1,
        InstrNode::new(Inst::Load {
            ty: Ty::Bool,
            ptr: ValueId::new(16),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(17)),
    );
    let mut body = bundle.module.clone();
    assert_eq!(
        body.proof_obligations.pop().unwrap().id,
        trust_ir::ProofId::new(1)
    );
    assert_eq!(
        body, expected,
        "only the exact typed two-cell test mutation and attached contract may differ"
    );
    let requests =
        trust_wp_lib::trust_ir_body::trust_ir_native_bundle_to_body_verify_requests(&bundle)
            .unwrap();
    assert_eq!(
        serde_json::to_value(&requests).unwrap(),
        capture["requests"]
    );
    let results: Vec<trust_wp_lib::VerifyBundleResult> =
        serde_json::from_value(capture["results"].clone()).unwrap();
    trust_wp_lib::trust_ir_body::replay_trust_ir_body_contracts(&bundle, &results).unwrap();
    // A valid certificate is tied to the actual module and attached formula.
    let mut wrong = bundle.clone();
    let Inst::Store { ptr, .. } = &mut wrong.module.functions[0].blocks[3].body[0].inst else {
        panic!("store")
    };
    *ptr = ValueId::new(4);
    assert!(trust_wp_lib::trust_ir_body::replay_trust_ir_body_contracts(&wrong, &results).is_err());
    println!("exact two-cell native request regeneration/replay and transfer refusal PASS");
}
