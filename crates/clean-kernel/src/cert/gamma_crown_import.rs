// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! gamma-crown certificate import bridge.

use std::sync::{Arc, LazyLock};

use serde::{Deserialize, Serialize};

use crate::env::Environment;
use crate::expr::{Expr, MDataMap, MDataValue};
use crate::name::Name;
use crate::tc::TypeChecker;
use crate::TypeError;

use super::ProofCert;

static NAME_TRUSTED_AY: LazyLock<Name> = LazyLock::new(|| Name::from_string("trustedAy"));
static META_NETWORK_NAME: LazyLock<Name> =
    LazyLock::new(|| Name::from_string("gamma_crown.network_name"));
static META_PROPERTY: LazyLock<Name> = LazyLock::new(|| Name::from_string("gamma_crown.property"));
static META_BOUND_TYPE: LazyLock<Name> =
    LazyLock::new(|| Name::from_string("gamma_crown.bound_type"));
static META_EPSILON: LazyLock<Name> = LazyLock::new(|| Name::from_string("gamma_crown.epsilon"));
static META_VERIFIED: LazyLock<Name> = LazyLock::new(|| Name::from_string("gamma_crown.verified"));
static META_COUNTEREXAMPLE: LazyLock<Name> =
    LazyLock::new(|| Name::from_string("gamma_crown.counterexample"));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum GammaCrownBoundType {
    #[serde(rename = "IBP", alias = "ibp")]
    Ibp,
    #[serde(rename = "CROWN", alias = "crown")]
    Crown,
    #[serde(
        rename = "alpha-CROWN",
        alias = "alpha_crown",
        alias = "alpha-crown",
        alias = "ALPHA_CROWN"
    )]
    AlphaCrown,
}

impl GammaCrownBoundType {
    fn as_str(self) -> &'static str {
        match self {
            Self::Ibp => "IBP",
            Self::Crown => "CROWN",
            Self::AlphaCrown => "alpha-CROWN",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[must_use = "gamma-crown certificates should be imported or stored"]
pub struct GammaCrownCert {
    pub network_name: String,
    pub property: String,
    pub bound_type: GammaCrownBoundType,
    pub epsilon: f64,
    pub verified: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<Vec<f64>>,
}

impl GammaCrownCert {
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    pub fn validate(&self) -> Result<(), GammaCrownImportError> {
        if self.network_name.trim().is_empty() {
            return Err(GammaCrownImportError::EmptyNetworkName);
        }
        if self.property.trim().is_empty() {
            return Err(GammaCrownImportError::EmptyProperty);
        }
        if !self.epsilon.is_finite() || self.epsilon < 0.0 {
            return Err(GammaCrownImportError::InvalidEpsilon(self.epsilon));
        }
        match (self.verified, &self.counterexample) {
            (true, Some(_)) => return Err(GammaCrownImportError::VerifiedHasCounterexample),
            (false, None) => return Err(GammaCrownImportError::MissingCounterexample),
            _ => {}
        }
        if let Some(counterexample) = &self.counterexample {
            for (index, value) in counterexample.iter().copied().enumerate() {
                if !value.is_finite() {
                    return Err(GammaCrownImportError::InvalidCounterexampleValue { index, value });
                }
            }
        }
        Ok(())
    }

    pub fn to_proof_cert(&self, env: &Environment) -> Result<ProofCert, GammaCrownImportError> {
        self.validate()?;
        if !self.verified {
            return Err(GammaCrownImportError::NotVerified);
        }

        let property_name = Name::from_string(&self.property);
        let property_expr = Expr::const_(property_name.clone(), Vec::<crate::level::Level>::new());
        let property_level =
            TypeChecker::new(env)
                .infer_sort(&property_expr)
                .map_err(|source| GammaCrownImportError::InvalidProperty {
                    property: self.property.clone(),
                    source,
                })?;
        let property_type = env.instantiate_type(&property_name, &[]).ok_or_else(|| {
            GammaCrownImportError::InvalidProperty {
                property: self.property.clone(),
                source: TypeError::UnknownConst(property_name.clone()),
            }
        })?;
        let trusted_type = env
            .instantiate_type(&NAME_TRUSTED_AY, std::slice::from_ref(&property_level))
            .ok_or(GammaCrownImportError::MissingTrustedBridge)?;

        let inner_cert = ProofCert::App {
            fn_cert: Box::new(ProofCert::Const {
                name: NAME_TRUSTED_AY.clone(),
                levels: vec![property_level],
                type_: Box::new(trusted_type.clone()),
            }),
            fn_type: Box::new(trusted_type),
            arg_cert: Box::new(ProofCert::Const {
                name: property_name,
                levels: vec![],
                type_: Box::new(property_type),
            }),
            result_type: Box::new(property_expr.clone()),
        };

        Ok(ProofCert::MData {
            metadata: self.metadata()?,
            inner_cert: Box::new(inner_cert),
            result_type: Box::new(property_expr),
        })
    }

    fn metadata(&self) -> Result<MDataMap, GammaCrownImportError> {
        let mut metadata = Vec::with_capacity(6);
        metadata.push((
            META_NETWORK_NAME.clone(),
            MDataValue::String(Arc::from(self.network_name.as_str())),
        ));
        metadata.push((
            META_PROPERTY.clone(),
            MDataValue::String(Arc::from(self.property.as_str())),
        ));
        metadata.push((
            META_BOUND_TYPE.clone(),
            MDataValue::String(Arc::from(self.bound_type.as_str())),
        ));
        metadata.push((
            META_EPSILON.clone(),
            MDataValue::String(Arc::from(self.epsilon.to_string())),
        ));
        metadata.push((META_VERIFIED.clone(), MDataValue::Bool(self.verified)));
        if let Some(counterexample) = &self.counterexample {
            let encoded = serde_json::to_string(counterexample)
                .map_err(GammaCrownImportError::CounterexampleEncoding)?;
            metadata.push((
                META_COUNTEREXAMPLE.clone(),
                MDataValue::String(Arc::from(encoded)),
            ));
        }
        Ok(metadata)
    }
}

pub fn import_gamma_crown_cert(
    cert: &GammaCrownCert,
    env: &Environment,
) -> Result<ProofCert, GammaCrownImportError> {
    cert.to_proof_cert(env)
}

pub fn import_gamma_crown_cert_json(
    json: &str,
    env: &Environment,
) -> Result<ProofCert, GammaCrownImportError> {
    let cert = GammaCrownCert::from_json(json).map_err(GammaCrownImportError::Json)?;
    cert.to_proof_cert(env)
}

#[derive(Debug, thiserror::Error)]
pub enum GammaCrownImportError {
    #[error("gamma-crown certificate has an empty network_name")]
    EmptyNetworkName,
    #[error("gamma-crown certificate has an empty property")]
    EmptyProperty,
    #[error("gamma-crown epsilon must be finite and non-negative, got {0}")]
    InvalidEpsilon(f64),
    #[error("verified gamma-crown certificates cannot carry a counterexample")]
    VerifiedHasCounterexample,
    #[error("unverified gamma-crown certificates must carry a counterexample")]
    MissingCounterexample,
    #[error("gamma-crown certificate is not verified")]
    NotVerified,
    #[error("counterexample entry {index} is not finite: {value}")]
    InvalidCounterexampleValue { index: usize, value: f64 },
    #[error("property {property:?} is not a well-formed Lean type: {source}")]
    InvalidProperty {
        property: String,
        #[source]
        source: TypeError,
    },
    #[error("trustedAy is not registered in the environment")]
    MissingTrustedBridge,
    #[error("failed to encode gamma-crown counterexample metadata: {0}")]
    CounterexampleEncoding(#[source] serde_json::Error),
    #[error("failed to parse gamma-crown certificate JSON: {0}")]
    Json(#[source] serde_json::Error),
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::cert::CertVerifier;
    use crate::env::{Declaration, Environment};
    use crate::level::Level;

    fn add_goal(env: &mut Environment, name: &str) {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("test goal declaration should register");
    }

    fn verified_cert() -> GammaCrownCert {
        GammaCrownCert {
            network_name: "mnist_small".to_string(),
            property: "Issue572.robust_goal".to_string(),
            bound_type: GammaCrownBoundType::AlphaCrown,
            epsilon: 0.125,
            verified: true,
            counterexample: None,
        }
    }

    #[test]
    fn gamma_crown_cert_json_round_trip() {
        let cert = verified_cert();
        let json = cert.to_json().expect("serialize gamma-crown cert");
        assert!(json.contains("\"bound_type\":\"alpha-CROWN\""));

        let restored = GammaCrownCert::from_json(&json).expect("deserialize gamma-crown cert");
        assert_eq!(restored, cert);
    }

    #[test]
    fn gamma_crown_bound_type_alias_deserializes() {
        let cert: GammaCrownCert = serde_json::from_str(
            r#"{
                "network_name":"net",
                "property":"Issue572.robust_goal",
                "bound_type":"alpha_crown",
                "epsilon":0.25,
                "verified":false,
                "counterexample":[0.0,1.0]
            }"#,
        )
        .expect("deserialize gamma-crown alias");

        assert_eq!(cert.bound_type, GammaCrownBoundType::AlphaCrown);
    }

    #[test]
    fn gamma_crown_import_builds_replayable_proof_cert() {
        let mut env = Environment::new();
        add_goal(&mut env, "Issue572.robust_goal");

        let cert = verified_cert();
        let proof = import_gamma_crown_cert(&cert, &env).expect("import verified gamma-crown cert");

        match &proof {
            ProofCert::MData {
                metadata,
                inner_cert,
                result_type,
            } => {
                assert_eq!(metadata.len(), 5);
                assert_eq!(
                    result_type.as_ref(),
                    &Expr::const_(
                        Name::from_string("Issue572.robust_goal"),
                        Vec::<Level>::new()
                    )
                );
                assert!(matches!(inner_cert.as_ref(), ProofCert::App { .. }));
            }
            other => panic!("expected MData proof cert, got {other:?}"),
        }

        let mut verifier = CertVerifier::new(&env);
        let (_replayed, verified_ty) = verifier
            .replay_and_verify(&proof)
            .expect("replay imported gamma-crown cert");
        assert_eq!(
            verified_ty,
            Expr::const_(
                Name::from_string("Issue572.robust_goal"),
                Vec::<Level>::new()
            )
        );
    }

    #[test]
    fn gamma_crown_import_rejects_unverified_certificates() {
        let mut env = Environment::new();
        add_goal(&mut env, "Issue572.robust_goal");

        let cert = GammaCrownCert {
            verified: false,
            counterexample: Some(vec![0.5, 0.25]),
            ..verified_cert()
        };

        let err = import_gamma_crown_cert(&cert, &env).expect_err("reject unverified cert");
        assert!(matches!(err, GammaCrownImportError::NotVerified));
    }

    #[test]
    fn gamma_crown_import_requires_counterexample_for_failures() {
        let mut env = Environment::new();
        add_goal(&mut env, "Issue572.robust_goal");

        let cert = GammaCrownCert {
            verified: false,
            counterexample: None,
            ..verified_cert()
        };

        let err = import_gamma_crown_cert(&cert, &env).expect_err("reject missing counterexample");
        assert!(matches!(err, GammaCrownImportError::MissingCounterexample));
    }
}
