// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The calculus row and the refutation evidence of `p3_planted_e9.rs`, installed
//! beside it (`p3_planted_e9/evidence.rs`).

use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceKernel, TheoryId,
};
use sha2::{Digest, Sha256};
use trust_certify::calculus_row::{
    self, CalculusRowClaim, Vf5Reference, certify_calculus_row, test_support,
};
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

use crate::contract::Outcome;
use crate::{CALCULUS_ARTIFACT, LINEAGE_DOMAIN};

pub(crate) fn konst(name: &str) -> Expr {
    Expr::const_str(name)
}

fn konst_at(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

fn list_nat() -> Expr {
    Expr::app(konst_at("List", vec![Level::zero()]), konst("Nat"))
}

fn pi(ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body)
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn eq_true(lhs: Expr) -> Expr {
    Expr::apps(
        konst_at("Eq", vec![Level::succ(Level::zero())]),
        [konst("Bool"), lhs, konst("Bool.true")],
    )
}

fn definition(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    }
}

/// A VF5-shaped STAND-IN family over a clone of `env`, in the shape of
/// `calculus_row::test_support::toy_kernel` with the annotation binder typed
/// `annotation_type`: `checkBlob` and `rowShape` always true, `RowProved _ _ _
/// _ := row_prop`, and `row_of .. _ _ := witness`. Admitted under a pin of its
/// own digest (`test_support::pin_own_digest`), which no production pin is.
pub(crate) fn calculus_base(
    env: &Environment,
    annotation_type: &str,
    row_prop: &str,
    witness: &str,
) -> Result<Vf5Reference, String> {
    if env.get_const(&Name::from_string(witness)).is_none() {
        return Err(format!("{witness} absent: row_of has no witness to cite"));
    }
    let mut base = env.clone();
    let a = || konst(annotation_type);
    let decls = [
        definition(
            "VF5.checkBlob",
            pi(list_nat(), pi(a(), pi(konst("Nat"), konst("Bool")))),
            lam(list_nat(), lam(a(), lam(konst("Nat"), konst("Bool.true")))),
        ),
        definition(
            "VF5.rowShape",
            pi(list_nat(), pi(a(), pi(konst("Nat"), pi(list_nat(), konst("Bool"))))),
            lam(list_nat(), lam(a(), lam(konst("Nat"), lam(list_nat(), konst("Bool.true"))))),
        ),
        definition(
            "VF5.RowProved",
            pi(list_nat(), pi(a(), pi(konst("Nat"), pi(list_nat(), Expr::prop())))),
            lam(list_nat(), lam(a(), lam(konst("Nat"), lam(list_nat(), konst(row_prop))))),
        ),
    ];
    for decl in decls {
        base.add_decl(decl)
            .map_err(|error| format!("the stand-in family is refused: {error:?}"))?;
    }
    // Binders, outermost first: bs A cs fid sym h hs.
    let check =
        eq_true(Expr::apps(konst("VF5.checkBlob"), [Expr::bvar(4), Expr::bvar(3), Expr::bvar(2)]));
    let shape = eq_true(Expr::apps(
        konst("VF5.rowShape"),
        [Expr::bvar(5), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)],
    ));
    let row = Expr::apps(
        konst("VF5.RowProved"),
        [Expr::bvar(6), Expr::bvar(5), Expr::bvar(3), Expr::bvar(2)],
    );
    let binders = |tail: Expr, wrap: fn(Expr, Expr) -> Expr| {
        wrap(list_nat(), wrap(a(), wrap(konst("Nat"), wrap(konst("Nat"), wrap(list_nat(), tail)))))
    };
    let type_ = binders(pi(check.clone(), pi(shape.clone(), row)), pi);
    let value = binders(lam(check, lam(shape, konst(witness))), lam);
    base.add_decl(Declaration::Theorem {
        name: Name::from_string("VF5.row_of"),
        level_params: vec![],
        type_,
        value,
    })
    .map_err(|error| format!("the stand-in row_of is refused: {error:?}"))?;
    let kernel = ReferenceKernel::new(base)
        .map_err(|refusal| format!("the entry refused the base: {refusal:?}"))?;
    test_support::pin_own_digest(kernel).map_err(|miss| format!("pin_own_digest: {miss:?}"))
}

/// One calculus row end to end: the certificate, then the compiler's bound
/// lookup (`calculus_row_certificate_bound`, which its `CalculusRowProved`
/// mint reads).
pub(crate) fn calculus_lane(
    reference: &Vf5Reference,
    symbol: &[u8],
    annotation: &Expr,
    failures: &mut Vec<String>,
) -> Result<[(Outcome, String); 2], String> {
    let claim =
        CalculusRowClaim { artifact: CALCULUS_ARTIFACT.to_vec(), fid: 0, symbol: symbol.to_vec() };
    let certificate = certify_calculus_row(reference, &claim, annotation, &Expr::nat_lit(0))
        .map_err(|miss| format!("{miss:?}"))?;
    let theory = certificate.reference().theory_id();
    if theory != TheoryId::LeanReferenceV1 {
        failures.push(format!("P3 UNEXPECTED THEORY: the calculus certificate names {theory:?}"));
    }
    let certified =
        (Outcome::Minted, format!("CalculusRowCertificate (ReferenceCertificate in {theory:?})"));
    calculus_row::register(certificate.clone());
    let registered = match calculus_row::calculus_row_certificate_bound(symbol, CALCULUS_ARTIFACT) {
        Some(found) if found == certificate => (
            Outcome::Minted,
            "calculus_row_certificate_bound returns it, the precondition of the compiler's CalculusRowProved mint"
                .to_string(),
        ),
        Some(other) => {
            failures.push(format!(
                "P3 UNEXPECTED CERTIFICATE: the bound lookup returned {other:?}, not the one registered"
            ));
            (Outcome::Refused, "calculus_row_certificate_bound returned another certificate".to_string())
        }
        None => (Outcome::Refused, "calculus_row_certificate_bound returned None".to_string()),
    };
    if calculus_row::calculus_row_certificate_bound(symbol, b"other artifact bytes").is_some() {
        failures.push(
            "P3 UNEXPECTED CERTIFICATE: the bound lookup ignored the artifact bytes".to_string(),
        );
    }
    Ok([certified, registered])
}

/// The violation `x < 0 ∧ 0 < x` over `Int`, the linear-Int lane's shape.
pub(crate) fn refutation_vc(function: &str) -> VerificationCondition {
    let x = || Formula::Var("p3_refutation_x".into(), Sort::Int);
    VerificationCondition {
        kind: VcKind::Assertion { message: "p3 refutation fixture".into() },
        function: trust_types::Symbol::intern(function),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

/// Trust's `CleanCic` lineage digest (`lineage_digest` over
/// `ObligationIdentity::from_vc`), reimplemented: SHA-256 over the domain tag
/// and the length-prefixed term, context and `vc:\0`-tagged bincode VC. It is
/// unkeyed, so it binds a payload to a row but does not authenticate who
/// produced it; the honest cold replay control checks this copy is exact.
fn lineage(term: &[u8], context: &[u8], vc: &VerificationCondition) -> trust_ir::ProofDigest {
    let mut identity = b"vc:\0".to_vec();
    bincode::serialize_into(&mut identity, vc).expect("a verification condition serializes");
    let mut hasher = Sha256::new();
    hasher.update(LINEAGE_DOMAIN);
    for field in [term, context, identity.as_slice()] {
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    trust_ir::ProofDigest::sha256(hasher.finalize().into())
}

/// `evidence` presented for `vc` with its term replaced by `term`.
pub(crate) fn presented(
    evidence: &trust_ir::ProofEvidence,
    term: Option<Vec<u8>>,
    vc: &VerificationCondition,
) -> Option<trust_ir::ProofEvidence> {
    let mut evidence = evidence.clone();
    let trust_ir::ProofEvidence::CleanCic { term: bytes, context, lineage: digest, .. } =
        &mut evidence
    else {
        return None;
    };
    if let Some(term) = term {
        *bytes = term;
    }
    *digest = lineage(bytes, context, vc);
    Some(evidence)
}

/// A yes/no entry's answer as a row: `entry` and what it returned.
pub(crate) fn verdict(minted: bool, entry: &str, (yes, no): (&str, &str)) -> (Outcome, String) {
    if minted {
        (Outcome::Minted, format!("{entry} {yes}"))
    } else {
        (Outcome::Refused, format!("{entry} {no}"))
    }
}

pub(crate) const RETURNED_BOOL: (&str, &str) = ("returned true", "returned false");
pub(crate) const RETURNED_SOME: (&str, &str) = ("returned a certificate", "returned None");
