// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean runtime ABI for the `ExternCalls` lowering of the trust-ir backend.
//!
//! In `RuntimeLowering::ExternCalls` mode the managed-runtime ops that the
//! `Dialect` mode emits as opaque `clean.*` nodes are instead lowered to
//! `Inst::Call`s targeting the **same** C runtime symbols `emit_c` calls
//! (`clean_alloc_ctor`, `clean_ctor_get`, …). trust-cg compiles those calls to
//! undefined external symbols, resolved at link time against the Clean runtime
//! — so the emitted module is real, compilable native code rather than an
//! un-lowerable dialect. (Perceus RC ops are the exception: they are native
//! trust-ir `Retain`/`Release`/`IsUnique` in every mode — P1 native ARC — and
//! only the RC-runtime import *triple* is declared here as their routing
//! contract; see [`RuntimeAbi`].)
//!
//! The native ARC routing triple is present in every external-runtime module.
//! Other helpers are declared at their actual first use, after the reserved
//! user rows and before boundary wrappers. Each call and its source evidence
//! share its original module-local slot.

use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir_build::ModuleBuilder;

/// A helper that an emitted instruction or its source evidence actually names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RuntimeImport {
    Box,
    BoxUint32,
    BoxUint64,
    NatOfU64,
    NatBig,
    NatLimbStep,
    BoxFloat,
    UnboxUint32,
    UnboxUint64,
    UnboxFloat,
    ObjTag,
    CtorGet,
    CtorGetUsize,
    CtorSet,
    CtorSetUsize,
    CtorSetTag,
    Reset,
    AllocCtor,
    Reuse,
    AllocClosure,
    MkStringFromBytes,
    ScalarGet(ScalarWidth),
    ScalarSet(ScalarWidth),
    Apply(usize),
}

/// Scalar field width in the runtime getter and setter interfaces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScalarWidth {
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

impl ScalarWidth {
    fn runtime_type(self) -> (&'static str, Ty) {
        match self {
            Self::U8 => ("uint8", Ty::U8),
            Self::U16 => ("uint16", Ty::U16),
            Self::U32 => ("uint32", Ty::U32),
            Self::U64 => ("uint64", Ty::U64),
            Self::F32 => ("float32", Ty::F32),
            Self::F64 => ("float", Ty::F64),
        }
    }
}

impl RuntimeImport {
    pub(crate) fn declare(self, mb: &mut ModuleBuilder, clean_fn_ty: FuncTyId) -> FuncId {
        let (name, params, returns, variadic): (String, Vec<Ty>, Vec<Ty>, bool) = match self {
            Self::Box => ("clean_box".into(), vec![Ty::U64], vec![Ty::Ptr], false),
            Self::BoxUint32 => (
                "clean_box_uint32".into(),
                vec![Ty::U32],
                vec![Ty::Ptr],
                false,
            ),
            Self::BoxUint64 => (
                "clean_box_uint64".into(),
                vec![Ty::U64],
                vec![Ty::Ptr],
                false,
            ),
            Self::NatOfU64 => (
                "clean_nat_of_u64".into(),
                vec![Ty::U64],
                vec![Ty::Ptr],
                false,
            ),
            Self::NatBig => (
                "clean_nat_big".into(),
                vec![Ty::U64, Ty::U64],
                vec![Ty::Ptr],
                false,
            ),
            Self::NatLimbStep => (
                "clean_nat_limb_step".into(),
                vec![Ty::Ptr, Ty::U64],
                vec![Ty::Ptr],
                false,
            ),
            Self::BoxFloat => (
                "clean_box_float".into(),
                vec![Ty::F64],
                vec![Ty::Ptr],
                false,
            ),
            Self::UnboxUint32 => (
                "clean_unbox_uint32".into(),
                vec![Ty::Ptr],
                vec![Ty::U32],
                false,
            ),
            Self::UnboxUint64 => (
                "clean_unbox_uint64".into(),
                vec![Ty::Ptr],
                vec![Ty::U64],
                false,
            ),
            Self::UnboxFloat => (
                "clean_unbox_float".into(),
                vec![Ty::Ptr],
                vec![Ty::F64],
                false,
            ),
            Self::ObjTag => ("clean_obj_tag".into(), vec![Ty::Ptr], vec![Ty::U32], false),
            Self::CtorGet => (
                "clean_ctor_get".into(),
                vec![Ty::Ptr, Ty::U64],
                vec![Ty::Ptr],
                false,
            ),
            Self::CtorGetUsize => (
                "clean_ctor_get_usize".into(),
                vec![Ty::Ptr, Ty::U32],
                vec![Ty::U64],
                false,
            ),
            Self::CtorSet => (
                "clean_ctor_set".into(),
                vec![Ty::Ptr, Ty::U64, Ty::Ptr],
                vec![],
                false,
            ),
            Self::CtorSetUsize => (
                "clean_ctor_set_usize".into(),
                vec![Ty::Ptr, Ty::U32, Ty::U64],
                vec![],
                false,
            ),
            Self::CtorSetTag => (
                "clean_ctor_set_tag".into(),
                vec![Ty::Ptr, Ty::U8],
                vec![],
                false,
            ),
            Self::Reset => ("clean_reset".into(), vec![Ty::Ptr], vec![Ty::Ptr], false),
            Self::AllocCtor => (
                "clean_alloc_ctor".into(),
                vec![Ty::U32, Ty::U32, Ty::U32],
                vec![Ty::Ptr],
                true,
            ),
            Self::Reuse => (
                "clean_reuse".into(),
                vec![Ty::Ptr, Ty::U32, Ty::U32, Ty::U32],
                vec![Ty::Ptr],
                true,
            ),
            Self::AllocClosure => (
                "clean_alloc_closure".into(),
                vec![Ty::Func(clean_fn_ty), Ty::U32, Ty::U32],
                vec![Ty::Ptr],
                true,
            ),
            Self::MkStringFromBytes => (
                "clean_mk_string_from_bytes".into(),
                vec![Ty::Ptr, Ty::U64],
                vec![Ty::Ptr],
                false,
            ),
            Self::ScalarGet(width) => {
                let (suffix, ty) = width.runtime_type();
                (
                    format!("clean_ctor_get_{suffix}"),
                    vec![Ty::Ptr, Ty::U32],
                    vec![ty],
                    false,
                )
            }
            Self::ScalarSet(width) => {
                let (suffix, ty) = width.runtime_type();
                (
                    format!("clean_ctor_set_{suffix}"),
                    vec![Ty::Ptr, Ty::U32, ty],
                    vec![],
                    false,
                )
            }
            Self::Apply(arity) => (
                format!("clean_apply_{arity}"),
                vec![Ty::Ptr; arity + 1],
                vec![Ty::Ptr],
                false,
            ),
        };
        let ty = if variadic {
            mb.add_vararg_func_type(params, returns)
        } else {
            mb.add_func_type(params, returns)
        };
        mb.declare_function(name, ty)
    }
}

/// All function bodies share a single ordered import table. User ids have
/// already been fixed when the first helper is requested.
#[derive(Clone, Debug)]
pub(crate) struct RuntimeAbi {
    pub(crate) clean_fn_ty: FuncTyId,
    first_import: u32,
    used: std::rc::Rc<std::cell::RefCell<Vec<RuntimeImport>>>,
}

impl RuntimeAbi {
    /// The native ARC operations refer to this complete routing triple
    /// implicitly. Its declarations are compulsory even without direct calls.
    pub(crate) fn declare_arc(mb: &mut ModuleBuilder) {
        let update = mb.add_func_type(vec![Ty::Ptr], vec![]);
        mb.declare_function("clean_inc", update);
        mb.declare_function("clean_dec", update);
        let exclusive = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U8]);
        mb.declare_function("clean_is_exclusive", exclusive);
    }

    pub(crate) fn new(mb: &mut ModuleBuilder, first_import: u32) -> Self {
        Self {
            clean_fn_ty: mb.add_func_type(vec![], vec![]),
            first_import,
            used: Default::default(),
        }
    }

    pub(crate) fn import(&self, role: RuntimeImport) -> FuncId {
        let mut used = self.used.borrow_mut();
        let ordinal = match used.iter().position(|entry| *entry == role) {
            Some(i) => i,
            None => {
                let i = used.len();
                used.push(role);
                i
            }
        };
        // Each import comes from the finite helper interface. If even this
        // suffix exhausts the FuncId space, finish refuses before publication.
        let id = u32::try_from(ordinal)
            .ok()
            .and_then(|i| self.first_import.checked_add(i));
        FuncId::new(id.unwrap_or(u32::MAX))
    }

    pub(crate) fn finish(
        self,
        mb: &mut ModuleBuilder,
    ) -> Result<Vec<RuntimeImport>, super::emit_trust_ir::TrustIrError> {
        use super::emit_trust_ir::TrustIrError;
        let used = std::mem::take(&mut *self.used.borrow_mut());
        for (i, &role) in used.iter().enumerate() {
            let expected = u32::try_from(i)
                .ok()
                .and_then(|i| self.first_import.checked_add(i))
                .ok_or_else(|| {
                    TrustIrError::Unsupported("runtime import FuncId space exhausted".into())
                })?;
            let id = role.declare(mb, self.clean_fn_ty);
            if id.index() != expected {
                return Err(TrustIrError::Unsupported(
                    "runtime import differs from its original call slot".into(),
                ));
            }
        }
        Ok(used)
    }

    /// Map a trust-ir scalar [`Ty`] to its [`ScalarWidth`], if it is a scalar.
    pub(crate) fn scalar_width(ty: &Ty) -> Option<ScalarWidth> {
        Some(match ty {
            Ty::U8 | Ty::I8 | Ty::Bool => ScalarWidth::U8,
            Ty::U16 | Ty::I16 => ScalarWidth::U16,
            Ty::U32 | Ty::I32 => ScalarWidth::U32,
            Ty::U64 | Ty::I64 => ScalarWidth::U64,
            Ty::F32 => ScalarWidth::F32,
            Ty::F64 => ScalarWidth::F64,
            _ => return None,
        })
    }
}
