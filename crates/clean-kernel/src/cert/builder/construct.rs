// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate constructors: primitive and compound node builders.

use std::sync::Arc;

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::level::Level;
use crate::name::Name;

use super::super::{CertError, ProofCert};
use super::state::{BuildResult, CertBuilder, NodeId};

impl<'env> CertBuilder<'env> {
    // Primitive constructors

    /// Build a Sort certificate for a universe level
    pub fn sort(&mut self, level: Level) -> BuildResult {
        let cert = ProofCert::Sort {
            level: level.clone(),
        };
        let computed_type = Expr::from_kind(ExprKind::Sort(Level::succ(level)));
        self.add_node(cert, computed_type)
    }

    /// Build a Const certificate for a constant reference
    pub fn const_(&mut self, name: impl Into<Name>, levels: Vec<Level>) -> BuildResult {
        let name = name.into();
        let instantiated_type = self
            .env
            .instantiate_type(&name, &levels)
            .ok_or_else(|| CertError::UnknownConst(name.clone()))?;

        let cert = ProofCert::Const {
            name: name.clone(),
            levels: levels.clone(),
            type_: Box::new(instantiated_type.clone()),
        };
        self.add_node(cert, instantiated_type)
    }

    /// Build a BVar certificate for a bound variable
    pub fn bvar(&mut self, idx: u32) -> BuildResult {
        let depth = self.context.len();
        if (idx as usize) >= depth {
            return Err(CertError::InvalidBVar(idx));
        }

        let level = depth - 1 - (idx as usize);
        let ctx_type = &self.context[level];

        #[allow(clippy::cast_possible_truncation)]
        let lift_amount = (depth - level) as u32;
        let lifted_type = ctx_type.lift(lift_amount);

        let cert = ProofCert::BVar {
            idx,
            expected_type: Box::new(lifted_type.clone()),
        };
        self.add_node(cert, lifted_type)
    }

    /// Build an FVar certificate for a free variable
    pub fn fvar(&mut self, id: FVarId) -> BuildResult {
        let type_ = self
            .fvar_types
            .get(&id)
            .ok_or(CertError::UnknownFVar(id))?
            .clone();

        let cert = ProofCert::FVar {
            id,
            type_: Box::new(type_.clone()),
        };
        self.add_node(cert, type_)
    }

    // Compound constructors

    /// Build an App certificate for function application
    pub fn app(&mut self, fn_id: NodeId, arg_id: NodeId) -> BuildResult {
        self.validate_node_id(fn_id, "App function")?;
        self.validate_node_id(arg_id, "App argument")?;

        let fn_cert = self.nodes[fn_id.index()].cert.clone();
        let fn_computed_type = self.nodes[fn_id.index()].computed_type.clone();
        let arg_cert = self.nodes[arg_id.index()].cert.clone();
        let arg_computed_type = self.nodes[arg_id.index()].computed_type.clone();

        let fn_type_whnf = self.whnf(&fn_computed_type);

        let (domain, codomain) = match &fn_type_whnf.kind {
            ExprKind::Pi(_, domain, codomain) => {
                (domain.as_ref().clone(), codomain.as_ref().clone())
            }
            _ => {
                return Err(CertError::StructureMismatch {
                    expected: "Pi type".to_string(),
                    actual: format!("{:?}", fn_type_whnf),
                });
            }
        };

        if !self.def_eq(&arg_computed_type, &domain) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(domain),
                actual: Box::new(arg_computed_type),
                location: "App argument".to_string(),
            });
        }

        let arg_expr = self.cert_to_expr(&arg_cert);
        let result_type = codomain.instantiate(&arg_expr);

        let cert = ProofCert::App {
            fn_cert: Box::new(fn_cert),
            fn_type: Box::new(fn_computed_type),
            arg_cert: Box::new(arg_cert),
            result_type: Box::new(result_type.clone()),
        };
        self.add_node(cert, result_type)
    }

    /// Build a Lam certificate for a lambda abstraction
    pub fn lam(
        &mut self,
        binder_info: BinderInfo,
        arg_type_id: NodeId,
        body_builder: impl FnOnce(&mut Self) -> BuildResult,
    ) -> BuildResult {
        self.validate_node_id(arg_type_id, "Lam arg_type")?;

        let arg_type_cert = self.nodes[arg_type_id.index()].cert.clone();
        let arg_type_computed = self.nodes[arg_type_id.index()].computed_type.clone();

        let arg_type_whnf = self.whnf(&arg_type_computed);
        if !matches!(arg_type_whnf.kind, ExprKind::Sort(_)) {
            return Err(CertError::StructureMismatch {
                expected: "Sort".to_string(),
                actual: format!("{:?}", arg_type_whnf),
            });
        }

        let arg_type_expr = self.cert_to_expr(&arg_type_cert);
        self.push_binder(arg_type_expr.clone());
        let body_result = body_builder(self);
        self.pop_binder();

        let body_id = body_result?;
        let body_cert = self.nodes[body_id.index()].cert.clone();
        let body_type_expr = self.nodes[body_id.index()].computed_type.clone();

        let result_type = Expr::from_kind(ExprKind::Pi(
            binder_info.into(),
            Arc::new(arg_type_expr.clone()),
            Arc::new(body_type_expr),
        ));

        let cert = ProofCert::Lam {
            binder_info,
            arg_type_cert: Box::new(arg_type_cert),
            body_cert: Box::new(body_cert),
            result_type: Box::new(result_type.clone()),
        };
        self.add_node(cert, result_type)
    }

    /// Build a Pi certificate for a dependent function type
    pub fn pi(
        &mut self,
        binder_info: BinderInfo,
        arg_type_id: NodeId,
        body_builder: impl FnOnce(&mut Self) -> BuildResult,
    ) -> BuildResult {
        self.validate_node_id(arg_type_id, "Pi arg_type")?;

        let arg_type_cert = self.nodes[arg_type_id.index()].cert.clone();
        let arg_type_computed = self.nodes[arg_type_id.index()].computed_type.clone();

        let arg_type_whnf = self.whnf(&arg_type_computed);
        let arg_level = match &arg_type_whnf.kind {
            ExprKind::Sort(l) => l.clone(),
            _ => {
                return Err(CertError::StructureMismatch {
                    expected: "Sort".to_string(),
                    actual: format!("{:?}", arg_type_whnf),
                });
            }
        };

        let arg_type_expr = self.cert_to_expr(&arg_type_cert);
        self.push_binder(arg_type_expr);
        let body_result = body_builder(self);
        self.pop_binder();

        let body_id = body_result?;
        let body_cert = self.nodes[body_id.index()].cert.clone();
        let body_computed = self.nodes[body_id.index()].computed_type.clone();

        let body_type_whnf = self.whnf(&body_computed);
        let body_level = match &body_type_whnf.kind {
            ExprKind::Sort(l) => l.clone(),
            _ => {
                return Err(CertError::StructureMismatch {
                    expected: "Sort (body type must be a type)".to_string(),
                    actual: format!("{:?}", body_type_whnf),
                });
            }
        };

        let result_type = Expr::from_kind(ExprKind::Sort(Level::imax(
            arg_level.clone(),
            body_level.clone(),
        )));

        let cert = ProofCert::Pi {
            binder_info,
            arg_type_cert: Box::new(arg_type_cert),
            arg_level,
            body_type_cert: Box::new(body_cert),
            body_level,
        };
        self.add_node(cert, result_type)
    }

    /// Build a Let certificate for a let binding
    pub fn let_(
        &mut self,
        type_id: NodeId,
        value_id: NodeId,
        body_builder: impl FnOnce(&mut Self) -> BuildResult,
    ) -> BuildResult {
        self.validate_node_id(type_id, "Let type")?;
        self.validate_node_id(value_id, "Let value")?;

        let type_cert = self.nodes[type_id.index()].cert.clone();
        let type_computed = self.nodes[type_id.index()].computed_type.clone();
        let value_cert = self.nodes[value_id.index()].cert.clone();
        let value_computed = self.nodes[value_id.index()].computed_type.clone();

        let type_whnf = self.whnf(&type_computed);
        if !matches!(type_whnf.kind, ExprKind::Sort(_)) {
            return Err(CertError::StructureMismatch {
                expected: "Sort".to_string(),
                actual: format!("{:?}", type_whnf),
            });
        }

        let type_expr = self.cert_to_expr(&type_cert);

        if !self.def_eq(&value_computed, &type_expr) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(type_expr.clone()),
                actual: Box::new(value_computed),
                location: "Let value".to_string(),
            });
        }

        let value_expr = self.cert_to_expr(&value_cert);
        self.push_binder(type_expr);
        let body_result = body_builder(self);
        self.pop_binder();

        let body_id = body_result?;
        let body_cert = self.nodes[body_id.index()].cert.clone();
        let body_computed = self.nodes[body_id.index()].computed_type.clone();

        let result_type = body_computed.instantiate(&value_expr);

        let cert = ProofCert::Let {
            type_cert: Box::new(type_cert),
            value_cert: Box::new(value_cert),
            body_cert: Box::new(body_cert),
            result_type: Box::new(result_type.clone()),
        };
        self.add_node(cert, result_type)
    }

    /// Build a DefEq certificate for type conversion via definitional equality
    pub fn def_eq_coerce(&mut self, inner_id: NodeId, expected_type: Expr) -> BuildResult {
        self.validate_node_id(inner_id, "DefEq inner")?;

        let inner_cert = self.nodes[inner_id.index()].cert.clone();
        let inner_computed = self.nodes[inner_id.index()].computed_type.clone();

        if !self.def_eq(&inner_computed, &expected_type) {
            return Err(CertError::DefEqFailed {
                left: Box::new(inner_computed),
                right: Box::new(expected_type),
            });
        }

        let cert = ProofCert::DefEq {
            inner: Box::new(inner_cert),
            expected_type: Box::new(expected_type.clone()),
            actual_type: Box::new(inner_computed),
            eq_steps: vec![],
        };
        self.add_node(cert, expected_type)
    }

    // Finalization

    /// Finish building and return the root certificate
    pub fn finish(self, root: NodeId) -> Result<ProofCert, CertError> {
        if root.index() >= self.nodes.len() {
            return Err(CertError::InvalidCert(format!(
                "Invalid root NodeId: {} (only {} nodes built)",
                root.raw(),
                self.nodes.len()
            )));
        }
        Ok(self.nodes[root.index()].cert.clone())
    }

    /// Get the certificate at the given node ID
    pub fn get_cert(&self, id: NodeId) -> Option<&ProofCert> {
        self.nodes.get(id.index()).map(|n| &n.cert)
    }
}
