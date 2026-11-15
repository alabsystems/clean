use trust_ir::Module;
use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::proof::{
    CoverageAssurance, CoverageBound, ObligationKind, ProofCertificate, ProofDigest, ProofEvidence,
    ProofFormula, ProofObligation, ProofStatus,
};
use trust_ir::value::ProofId;

#[test]
fn v41_new_obligation_kinds_and_certificate_assurance_round_trip() {
    let mut m = Module::new("kinds");
    for (i, kind) in [
        ObligationKind::Termination,
        ObligationKind::Ownership,
        ObligationKind::Custom {
            namespace: "trust.concurrency".into(),
            name: "data_race".into(),
        },
    ]
    .into_iter()
    .enumerate()
    {
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(i as u32),
            kind,
            ProofStatus::Pending,
            "k",
        ));
    }
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "trust-mc".into(),
        evidence: ProofEvidence::Trusted("audited".into()),
        assurance: Some(CoverageAssurance {
            bound: CoverageBound::UnwindBounded { depth: 1 },
            request_digest: ProofDigest::sha256([7u8; 32]),
        }),
    });

    let back = deserialize_module(&serialize_module(&m).expect("serialize_module: test fixture"))
        .expect("decode");
    assert_eq!(back, m, "kinds + assurance must survive binary");
    assert!(matches!(
        back.proof_obligations[2].kind,
        ObligationKind::Custom { .. }
    ));

    let j = serde_json::to_string(&m).unwrap();
    assert_eq!(serde_json::from_str::<Module>(&j).unwrap(), m, "json");
    let mp = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(
        rmp_serde::from_slice::<Module>(&mp).unwrap(),
        m,
        "positional msgpack"
    );
}

/// Two `Custom` kinds differing only in namespace must NOT share a digest —
/// otherwise two producers' obligations collide on one cert-cache slot.
#[test]
fn distinct_custom_namespaces_do_not_collide_in_the_digest() {
    let mk = |ns: &str| {
        let mut m = Module::new("d");
        m.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Custom {
                namespace: ns.into(),
                name: "x".into(),
            },
            ProofStatus::Pending,
            "k",
        ));
        m.stable_digest()
    };
    assert_ne!(
        mk("a.ns"),
        mk("b.ns"),
        "namespace must be part of the identity"
    );
}

#[test]
fn decreases_clauses_round_trip_on_a_summary() {
    use trust_ir::ty::{FuncTy, Ty};
    use trust_ir::value::FuncId;
    use trust_ir::{Function, FunctionSummary};
    let mut m = Module::new("dec");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut sum = FunctionSummary::new().with_params(vec!["n".into()]);
    sum.decreases.push(ProofFormula::smtlib2("n", "Int"));
    m.try_add_function(Function::declaration(FuncId::new(0), "f", ft, sum))
        .expect("Module::try_add_function: test fixture");
    let back = deserialize_module(&serialize_module(&m).expect("serialize_module: test fixture"))
        .expect("decode");
    assert_eq!(
        back.functions[0].summary.as_ref().unwrap().decreases.len(),
        1
    );
    assert_eq!(back, m);
}
