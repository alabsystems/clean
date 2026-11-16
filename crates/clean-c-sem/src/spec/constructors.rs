//! Smart constructors for the [`Spec`] assertion tree.
//!
//! The `impl Spec` constructor surface (`Spec::and`/`Spec::forall`/`Spec::ge`
//! ...) extracted from `spec.rs`; the ACSL data model itself — `Spec`,
//! `Location`, `Behavior`, `FuncSpec`, `LoopSpec`, `Annotation` — stays in the
//! parent module. Inherent `impl` blocks are module-independent, so every
//! constructor keeps its `Spec::` path.

use super::Spec;
use crate::expr::{BinOp, CExpr};
use crate::types::CType;

impl Spec {
    // Constructors

    pub fn true_() -> Self {
        Spec::True
    }

    pub fn false_() -> Self {
        Spec::False
    }

    pub fn result() -> Self {
        Spec::Result
    }

    pub fn old(e: Spec) -> Self {
        Spec::Old(Box::new(e))
    }

    pub fn var(name: impl Into<String>) -> Self {
        Spec::Var(name.into())
    }

    pub fn int(val: i64) -> Self {
        Spec::Int(val)
    }

    pub fn expr(e: CExpr) -> Self {
        Spec::Expr(e)
    }

    pub fn and(specs: Vec<Spec>) -> Self {
        if specs.is_empty() {
            Spec::True
        } else if specs.len() == 1 {
            specs
                .into_iter()
                .next()
                .expect("invariant: specs.len() == 1 checked above")
        } else {
            Spec::And(specs)
        }
    }

    pub fn or(specs: Vec<Spec>) -> Self {
        if specs.is_empty() {
            Spec::False
        } else if specs.len() == 1 {
            specs
                .into_iter()
                .next()
                .expect("invariant: specs.len() == 1 checked above")
        } else {
            Spec::Or(specs)
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn not(s: Spec) -> Self {
        Spec::Not(Box::new(s))
    }

    pub fn implies(p: Spec, q: Spec) -> Self {
        Spec::Implies(Box::new(p), Box::new(q))
    }

    pub fn iff(p: Spec, q: Spec) -> Self {
        Spec::Iff(Box::new(p), Box::new(q))
    }

    pub fn forall(var: impl Into<String>, ty: CType, body: Spec) -> Self {
        Spec::Forall {
            var: var.into(),
            ty,
            body: Box::new(body),
        }
    }

    pub fn exists(var: impl Into<String>, ty: CType, body: Spec) -> Self {
        Spec::Exists {
            var: var.into(),
            ty,
            body: Box::new(body),
        }
    }

    pub fn valid(ptr: Spec) -> Self {
        Spec::Valid(Box::new(ptr))
    }

    pub(crate) fn valid_read(ptr: Spec) -> Self {
        Spec::ValidRead(Box::new(ptr))
    }

    pub fn binop(op: BinOp, left: Spec, right: Spec) -> Self {
        Spec::BinOp {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Create a comparison
    pub fn eq(left: Spec, right: Spec) -> Self {
        Self::binop(BinOp::Eq, left, right)
    }

    pub fn ne(left: Spec, right: Spec) -> Self {
        Self::binop(BinOp::Ne, left, right)
    }

    pub fn lt(left: Spec, right: Spec) -> Self {
        Self::binop(BinOp::Lt, left, right)
    }

    pub fn le(left: Spec, right: Spec) -> Self {
        Self::binop(BinOp::Le, left, right)
    }

    pub fn gt(left: Spec, right: Spec) -> Self {
        Self::binop(BinOp::Gt, left, right)
    }

    pub fn ge(left: Spec, right: Spec) -> Self {
        Self::binop(BinOp::Ge, left, right)
    }
}
