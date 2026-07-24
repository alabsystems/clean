// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof certificate verification API.
//!
//! Extracted from `infer/mod.rs`. Contains methods for creating certificate
//! verifiers and performing certified type inference.

use super::*;
use clean_kernel::cert::{CertError, CertVerifier, ProofCert};

impl<'a> ElabCtx<'a> {
    /// Create a certificate verifier with the current local context pre-registered.
    ///
    /// This enables verification of elaborated expressions that contain free variables
    /// from the elaboration context. The verifier is initialized with all locals and
    /// metavariables from this context.
    ///
    /// # Example
    ///
    /// ```text
    /// let mut ctx = ElabCtx::new(&env);
    /// let expr = ctx.elaborate(&surface)?;
    /// let (ty, cert) = ctx.infer_type_with_cert(&expr)?;
    /// let verifier = ctx.create_cert_verifier()?;
    /// verifier.verify(&cert, &expr)?;
    /// ```
    pub fn create_cert_verifier(&self) -> Result<CertVerifier<'a>, CertError> {
        let mut verifier = CertVerifier::with_mode(self.env, self.env.mode());
        verifier.register_local_context(&self.build_local_ctx())?;
        Ok(verifier)
    }

    /// Infer the type of an expression with a proof certificate.
    ///
    /// This is the certified variant of `infer_type` - it returns both the inferred
    /// type and a proof certificate that can be independently verified.
    ///
    /// The certificate can be verified using a `CertVerifier` created from
    /// `create_cert_verifier()`.
    ///
    /// # REQUIRES
    /// - `expr` is a valid kernel expression (may contain metavariables)
    ///
    /// # ENSURES
    /// - On success, returns `(type, cert)` where `type` is the inferred type
    /// - Certificate is verifiable via `CertVerifier::verify(&cert)`
    /// - Metavariables in `expr` are instantiated before type checking
    pub fn infer_type_with_cert(&self, expr: &Expr) -> Result<(Expr, ProofCert), ElabError> {
        let tc =
            TypeChecker::with_context_and_mode(self.env, self.build_local_ctx(), self.env.mode());
        let instantiated = self.metas.instantiate(expr);
        let instantiated = self.metas.instantiate_levels(&instantiated);
        tc.infer_type_with_cert(&instantiated)
            .map(|(ty, cert)| {
                let ty = self.metas.instantiate(&ty);
                (self.metas.instantiate_levels(&ty), cert)
            })
            .map_err(|e| ElabError::TypeMismatch {
                expected: "valid type".to_string(),
                actual: format!("{e:?}"),
            })
    }

    /// Elaborate and verify an expression with certificates.
    ///
    /// This combines elaboration, type inference, and certificate verification
    /// into a single operation. Returns the elaborated expression, its type,
    /// and the proof certificate.
    ///
    /// This is useful for verified elaboration pipelines where you want to ensure
    /// the elaborated expression type-checks correctly.
    pub fn elaborate_and_verify(
        &mut self,
        surface: &SurfaceExpr,
    ) -> Result<(Expr, Expr, ProofCert), ElabError> {
        let expr = self.elaborate(surface)?;
        let (ty, cert) = self.infer_type_with_cert(&expr)?;

        // Verify the certificate
        let mut verifier = self
            .create_cert_verifier()
            .map_err(|e| ElabError::TypeMismatch {
                expected: "valid certificate verifier".to_string(),
                actual: format!("{e:?}"),
            })?;

        let _ = verifier
            .verify(&cert, &expr)
            .map_err(|e| ElabError::TypeMismatch {
                expected: "certificate verification".to_string(),
                actual: format!("{e:?}"),
            })?;

        Ok((expr, ty, cert))
    }
}
