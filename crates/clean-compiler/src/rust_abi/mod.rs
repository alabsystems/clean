// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A Lean function at the Rust ABI (Trust plan step 3.2).
//!
//! Trust compiles a crate whose Rust code calls Lean `def`s and whose Lean
//! `def`s call Rust `fn`s. The Trust design that sets this step
//! (`docs/design/2026-10-02-step3-lean-through-trust-ir.md`, §2 and §3) fixes
//! what such a Lean function becomes in trust-ir, and makes Clean's compiler —
//! this crate's general pipeline — its one producer:
//!
//! * **C1** — scalar primitives at the machine type (`a + b` at `UInt64` is
//!   one `add`), instance dictionaries at carrier types resolved
//!   (`crate::carrier_prims`, `crate::opt::resolve_carrier_prims`);
//! * **C2** — a call to a Rust function is a direct call at the carrier ABI
//!   to the symbol Trust supplies ([`RustCallee`]);
//! * **C3** — a Rust-callable function's signature IS its carrier signature
//!   (`carrier_signature`), and `Nat` is the pinned `trust_bignum::Nat`
//!   handle, never the bounded `Nat` of Clean's C runtime;
//! * **C4** — every emitted function is disclosed with a determinism digest
//!   (environment, declaration, core version, target) → Function.
//!
//! The entry point is `compile_rust_abi` (feature `trust-ir-backend`). Its
//! output is computational content only: proofs, types and every claim
//! channel are erased, no kernel term enters the module, and every body is
//! stamped `Ungated` — the authority to ship a body is Trust's carrier gate
//! (`trust-clean-ir-gate`), never this producer.

#[cfg(feature = "trust-ir-backend")]
mod compile;
#[cfg(feature = "trust-ir-backend")]
pub use compile::{compile_rust_abi, CoreFunctionDigest, RustAbiOutput, RustAbiRow};

use crate::ir::IRType;
use crate::lcnf::{Decl, DeclValue, ExternAttr, ExternEntry, Param};
use clean_kernel::env::ConstantKind;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};
use thiserror::Error;

/// The extern backend tag of a Rust callee (`ExternEntry::backend`).
pub(crate) const RUST_EXTERN_BACKEND: &str = "rust";

/// A carrier type: the closed vocabulary a Rust-callable Lean function may
/// mention in its signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Carrier {
    /// `Bool` at `bool`.
    Bool,
    /// `UInt8` at `u8`.
    UInt8,
    /// `UInt16` at `u16`.
    UInt16,
    /// `UInt32` at `u32`.
    UInt32,
    /// `UInt64` at `u64`.
    UInt64,
    /// `Nat` at the pinned `trust_bignum::Nat` handle.
    Nat,
}

impl Carrier {
    /// The carrier a kernel type names, if it is exactly one of the carriers.
    pub(crate) fn of_type(ty: &Expr) -> Option<Self> {
        let ExprKind::Const(name, levels) = ty.kind() else {
            return None;
        };
        if !levels.is_empty() {
            return None;
        }
        Some(match name.to_string().as_str() {
            "Bool" => Self::Bool,
            "UInt8" => Self::UInt8,
            "UInt16" => Self::UInt16,
            "UInt32" => Self::UInt32,
            "UInt64" => Self::UInt64,
            "Nat" => Self::Nat,
            _ => return None,
        })
    }

    /// The L5IR type of the carrier (`Nat` is an object until the emitter
    /// carries it as the pinned handle).
    pub(crate) fn ir_type(self) -> IRType {
        match self {
            Self::Bool => IRType::Bool,
            Self::UInt8 => IRType::UInt8,
            Self::UInt16 => IRType::UInt16,
            Self::UInt32 => IRType::UInt32,
            Self::UInt64 => IRType::UInt64,
            Self::Nat => IRType::Object,
        }
    }
}

/// A function's signature over carriers: what its emitted `FuncTy` must be.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarrierSignature {
    /// The parameter carriers, in order.
    pub params: Vec<Carrier>,
    /// The result carrier.
    pub result: Carrier,
}

/// Why a declaration cannot be compiled at the Rust ABI. Every refusal names
/// the declaration, the reason, and the options (Trust ruling v7/D3).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum RustAbiError {
    /// The declaration is not in the environment.
    #[error(
        "Rust ABI: `{name}` is not in the kernel environment. Options: declare it in the \
         island batch, or remove the reference."
    )]
    UnknownConstant {
        /// The missing declaration.
        name: String,
    },
    /// A signature position is not a carrier.
    #[error(
        "Rust ABI: `{name}` has {position} of type `{found}`, outside the carrier vocabulary \
         (Bool, UInt8, UInt16, UInt32, UInt64, Nat). Options: change the signature to \
         carrier types, or keep the declaration Lean-only (it is then not Rust-callable)."
    )]
    NotACarrier {
        /// The declaration.
        name: String,
        /// `parameter N` or `result`.
        position: String,
        /// The kernel type found there.
        found: String,
    },
    /// A Rust callee must be the opaque constant Trust declared for it.
    #[error(
        "Rust ABI: Rust callee `{name}` is a {kind}, not the opaque constant the Rust \
         compiler declares for a Rust `fn`. Its Lean value would be compiled instead of \
         calling Rust. Options: declare it with Trust's `declare_rust_callees`, or call the \
         Lean definition as a Lean function."
    )]
    RustCalleeNotOpaque {
        /// The callee.
        name: String,
        /// The kernel kind found.
        kind: String,
    },
    /// `Nat` has no Rust carrier ABI for a Rust callee.
    #[error(
        "Rust ABI: Rust callee `{name}` mentions `Nat`; a Rust `fn` is called at `bool` and \
         `u8`..`u64` only (Trust's `RustCallee` vocabulary). Options: give the Rust function \
         a machine-integer signature."
    )]
    RustCalleeNat {
        /// The callee.
        name: String,
    },
    /// The declaration has no computational content.
    #[error(
        "Rust ABI: `{name}` has no computational content (an axiom, theorem, noncomputable \
         or value-less constant). Options: give it a computable definition, or do not call \
         it from Rust."
    )]
    NotComputational {
        /// The declaration.
        name: String,
    },
    /// Two batch entries, or a batch entry and a primitive, share a name.
    #[error("Rust ABI: `{name}` {detail}")]
    Conflict {
        /// The contested name.
        name: String,
        /// What it conflicts with, and the options.
        detail: String,
    },
    /// The pipeline or the emitter refused the batch.
    #[error("Rust ABI: the core refused the batch: {detail}")]
    Refused {
        /// The rendered refusal, naming the declaration and construct.
        detail: String,
    },
    /// The emitted signature is not the declaration's carrier signature.
    #[error(
        "Rust ABI: `{name}` was emitted at `{emitted}`, not at its carrier signature \
         `{expected}`. Options: eta-expand the definition so every parameter is a lambda \
         binder, or report this pairing."
    )]
    SignatureMismatch {
        /// The declaration.
        name: String,
        /// The carrier signature, rendered.
        expected: String,
        /// The emitted function type, rendered.
        emitted: String,
    },
}

/// The carrier signature of the kernel constant `name`: every Pi binder and
/// the codomain must be a carrier.
///
/// # Errors
///
/// [`RustAbiError::UnknownConstant`] or [`RustAbiError::NotACarrier`].
pub(crate) fn carrier_signature(
    env: &Environment,
    name: &Name,
) -> Result<CarrierSignature, RustAbiError> {
    let info = env
        .get_const(name)
        .ok_or_else(|| RustAbiError::UnknownConstant {
            name: name.to_string(),
        })?;
    let refuse = |position: String, found: &Expr| RustAbiError::NotACarrier {
        name: name.to_string(),
        position,
        found: format!("{found:?}"),
    };
    let mut params = Vec::new();
    let mut ty = &info.type_;
    while let ExprKind::Pi(_, dom, body) = ty.kind() {
        let carrier = Carrier::of_type(dom)
            .ok_or_else(|| refuse(format!("parameter {}", params.len()), dom))?;
        params.push(carrier);
        ty = body;
    }
    let result = Carrier::of_type(ty).ok_or_else(|| refuse("result".to_string(), ty))?;
    Ok(CarrierSignature { params, result })
}

/// One Rust function a Lean island calls: the Clean constant Trust declared
/// for it (`trust_certify::clean_island::declare_rust_callees`, a kernel
/// `Opaque` with a hidden inhabitant) and the link-time symbol of the Rust
/// function (Trust's `tcx.symbol_name`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RustCallee {
    /// The Clean constant applications of which are calls to Rust.
    pub constant: Name,
    /// The Rust function's link-time symbol.
    pub symbol: String,
}

/// The L5CNF extern declaration through which a [`RustCallee`] enters the
/// pipeline: `Decl::extern_decl` with one `rust` entry naming the symbol, its
/// parameters and result at the callee's carrier signature.
///
/// The hidden inhabitant of the opaque is never compiled — the declaration
/// has no code body, so a call can only be the call to Rust.
///
/// # Errors
///
/// The constant is unknown, not `Opaque`, or not at a non-`Nat` carrier
/// signature.
pub(crate) fn rust_callee_decl(
    env: &Environment,
    callee: &RustCallee,
) -> Result<Decl, RustAbiError> {
    let name = &callee.constant;
    let info = env
        .get_const(name)
        .ok_or_else(|| RustAbiError::UnknownConstant {
            name: name.to_string(),
        })?;
    if info.kind != ConstantKind::Opaque {
        return Err(RustAbiError::RustCalleeNotOpaque {
            name: name.to_string(),
            kind: format!("{:?}", info.kind),
        });
    }
    let signature = carrier_signature(env, name)?;
    if signature.params.contains(&Carrier::Nat) || signature.result == Carrier::Nat {
        return Err(RustAbiError::RustCalleeNat {
            name: name.to_string(),
        });
    }
    let carrier_expr = |c: Carrier| -> Expr {
        let lean = match c {
            Carrier::Bool => "Bool",
            Carrier::UInt8 => "UInt8",
            Carrier::UInt16 => "UInt16",
            Carrier::UInt32 => "UInt32",
            Carrier::UInt64 => "UInt64",
            Carrier::Nat => "Nat",
        };
        Expr::const_str(lean)
    };
    let params = signature
        .params
        .iter()
        .enumerate()
        .map(|(i, c)| Param::new(FVarId::new(i as u64), Name::anon(), carrier_expr(*c)))
        .collect();
    Ok(Decl::extern_decl(
        name.clone(),
        info.level_params.clone(),
        carrier_expr(signature.result),
        params,
        vec![ExternEntry {
            backend: RUST_EXTERN_BACKEND.to_string(),
            name: callee.symbol.clone(),
        }],
    ))
}

/// The Rust symbol an extern declaration names, if it is a Rust callee.
pub(crate) fn rust_extern_symbol(attr: &ExternAttr) -> Option<&str> {
    attr.entries
        .iter()
        .find(|entry| entry.backend == RUST_EXTERN_BACKEND)
        .map(|entry| entry.name.as_str())
}

/// A Rust callee as the L5IR sees it: its Clean name, its symbol, and its
/// lowered signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RustExternSig {
    /// The Clean constant.
    pub(crate) name: Name,
    /// The Rust symbol.
    pub(crate) symbol: String,
    /// Lowered parameter types.
    pub(crate) params: Vec<IRType>,
    /// Lowered result type.
    pub(crate) ret: IRType,
}

impl RustExternSig {
    /// The signature of `decl` if it is a Rust-callee extern declaration.
    pub(crate) fn of_decl(decl: &Decl) -> Option<Self> {
        let DeclValue::Extern(attr) = &decl.body else {
            return None;
        };
        let symbol = rust_extern_symbol(attr)?;
        let params = decl
            .params
            .iter()
            .map(|p| Carrier::of_type(&p.ty).map(Carrier::ir_type))
            .collect::<Option<Vec<_>>>()?;
        let ret = Carrier::of_type(&decl.ty)?.ir_type();
        Some(Self {
            name: decl.name.clone(),
            symbol: symbol.to_string(),
            params,
            ret,
        })
    }
}
