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
//! [`RuntimeAbi`] declares every such symbol as a bodyless `Linkage::External`
//! import (valid per `validate_module`) and caches the resulting [`FuncId`]s.
//! It MUST be built before any user function is emitted, because trust-ir
//! assigns `FuncId`s sequentially and a live `FunctionBuilder` borrows the
//! `ModuleBuilder`.

use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir_build::ModuleBuilder;

/// Cached [`FuncId`]s of the declared Clean-runtime extern imports.
///
/// The RC ops themselves (`clean_inc` / `clean_dec` / `clean_is_exclusive`)
/// carry no cached ids: since P1 native ARC the emitter expresses Perceus RC
/// as trust-ir `Retain`/`Release`/`IsUnique` and never calls them directly.
/// [`RuntimeAbi::declare`] still declares that triple — it is the module's
/// RC-runtime *provenance*, the contract trust-cg's ARC lowering routes by
/// (and the symbols the lowered object then calls at run time).
#[derive(Debug, Clone)]
pub(crate) struct RuntimeAbi {
    pub(crate) clean_alloc_ctor: FuncId, // vararg
    pub(crate) clean_box: FuncId,
    pub(crate) clean_box_uint32: FuncId,
    pub(crate) clean_box_uint64: FuncId,
    pub(crate) clean_box_float: FuncId,
    /// `clean_nat_of_u64(u64) -> clean_obj*`: the SOUND `Nat`-from-scalar
    /// producer (RUNG B). A tagged immediate below 2^63, a heap Nat cell at or
    /// above it — unlike `clean_box`, which truncates a `Nat` carrier at bit 63.
    pub(crate) clean_nat_of_u64: FuncId,
    /// `clean_nat_big(lo: u64, hi: u64) -> clean_obj*`: a big `Nat` literal
    /// `>= 2^64` (`lo + hi*2^64`) as a heap Nat cell (RUNG B).
    pub(crate) clean_nat_big: FuncId,
    pub(crate) clean_unbox: FuncId,
    pub(crate) clean_unbox_uint32: FuncId,
    pub(crate) clean_unbox_uint64: FuncId,
    pub(crate) clean_unbox_float: FuncId,
    pub(crate) clean_obj_tag: FuncId,
    pub(crate) clean_ctor_get: FuncId,
    pub(crate) clean_ctor_get_usize: FuncId,
    pub(crate) clean_ctor_set: FuncId,
    pub(crate) clean_ctor_set_usize: FuncId,
    pub(crate) clean_ctor_set_tag: FuncId,
    pub(crate) clean_reset: FuncId,
    pub(crate) clean_reuse: FuncId, // vararg
    // Scalar field get/set, indexed by [`ScalarWidth`].
    pub(crate) scalar_get: [FuncId; 6],
    pub(crate) scalar_set: [FuncId; 6],
    // Closures.
    pub(crate) clean_alloc_closure: FuncId, // vararg; fn param typed Ty::Func(clean_fn_ty)
    pub(crate) apply: [FuncId; 33],         // clean_apply_0..=32
    pub(crate) clean_apply_n: FuncId,
    /// `clean_mk_string(const char*) -> clean_obj*`: builds a managed string
    /// from a NUL-terminated byte global (see the data-global pre-pass).
    pub(crate) clean_mk_string: FuncId,
    /// Canonical function type used for closure function pointers. Sharing one
    /// `Ty::Func` between `clean_alloc_closure`'s `fn` parameter and the
    /// `fn_addr` value lets the call type-check WITHOUT a `Ty::Func`->`Ty::Ptr`
    /// bitcast (which trust-cg lowers into a non-callable address).
    pub(crate) clean_fn_ty: FuncTyId,
    /// Number of extern functions declared (= the FuncId of the first user fn).
    pub(crate) n_externs: u32,
}

/// Index into [`RuntimeAbi::scalar_get`]/`scalar_set` for a scalar field width.
#[derive(Debug, Clone, Copy)]
pub(crate) enum ScalarWidth {
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

impl ScalarWidth {
    pub(crate) fn idx(self) -> usize {
        self as usize
    }
}

impl RuntimeAbi {
    /// Declare every runtime extern into `mb`. Must run before any user
    /// function is built so the extern `FuncId`s occupy `0..n_externs`.
    pub(crate) fn declare(mb: &mut ModuleBuilder) -> Self {
        let mut count: u32 = 0;
        // Non-capturing helpers (take `count` by &mut param so no closure holds
        // a long-lived borrow of it).
        fn ext(
            mb: &mut ModuleBuilder,
            count: &mut u32,
            name: &str,
            params: Vec<Ty>,
            rets: Vec<Ty>,
        ) -> FuncId {
            let ty = mb.add_func_type(params, rets);
            let id = mb.function(name, ty).build();
            *count += 1;
            id
        }
        fn ext_va(
            mb: &mut ModuleBuilder,
            count: &mut u32,
            name: &str,
            params: Vec<Ty>,
            rets: Vec<Ty>,
        ) -> FuncId {
            let ty = mb.add_vararg_func_type(params, rets);
            let id = mb.function(name, ty).build();
            *count += 1;
            id
        }
        let c = &mut count;
        let p = Ty::Ptr;
        // The RC-runtime import triple. Declared with EXACTLY these signatures
        // (clean_is_exclusive returns the C `bool` as U8) but never called by
        // the emitter: RC ops are native `Retain`/`Release`/`IsUnique` (P1
        // native ARC), and trust-cg's ARC lowering keys on a module declaring
        // this triple to route those ops to the Clean runtime. Do not remove
        // or retype these without coordinating with trust-cg's
        // `module_declares_clean_rc_runtime` contract.
        let clean_inc = ext(mb, c, "clean_inc", vec![p.clone()], vec![]);
        let _clean_dec = ext(mb, c, "clean_dec", vec![p.clone()], vec![]);
        let _clean_is_exclusive = ext(mb, c, "clean_is_exclusive", vec![p.clone()], vec![Ty::U8]);
        let clean_box = ext(mb, c, "clean_box", vec![Ty::U64], vec![p.clone()]);
        let clean_box_uint32 = ext(mb, c, "clean_box_uint32", vec![Ty::U32], vec![p.clone()]);
        let clean_box_uint64 = ext(mb, c, "clean_box_uint64", vec![Ty::U64], vec![p.clone()]);
        let clean_nat_of_u64 = ext(mb, c, "clean_nat_of_u64", vec![Ty::U64], vec![p.clone()]);
        let clean_nat_big = ext(
            mb,
            c,
            "clean_nat_big",
            vec![Ty::U64, Ty::U64],
            vec![p.clone()],
        );
        let clean_box_float = ext(mb, c, "clean_box_float", vec![Ty::F64], vec![p.clone()]);
        let clean_unbox = ext(mb, c, "clean_unbox", vec![p.clone()], vec![Ty::U64]);
        let clean_unbox_uint32 = ext(mb, c, "clean_unbox_uint32", vec![p.clone()], vec![Ty::U32]);
        let clean_unbox_uint64 = ext(mb, c, "clean_unbox_uint64", vec![p.clone()], vec![Ty::U64]);
        let clean_unbox_float = ext(mb, c, "clean_unbox_float", vec![p.clone()], vec![Ty::F64]);
        let clean_obj_tag = ext(mb, c, "clean_obj_tag", vec![p.clone()], vec![Ty::U8]);
        let clean_ctor_get = ext(
            mb,
            c,
            "clean_ctor_get",
            vec![p.clone(), Ty::U64],
            vec![p.clone()],
        );
        let clean_ctor_get_usize = ext(
            mb,
            c,
            "clean_ctor_get_usize",
            vec![p.clone(), Ty::U32],
            vec![Ty::U64],
        );
        let clean_ctor_set = ext(
            mb,
            c,
            "clean_ctor_set",
            vec![p.clone(), Ty::U64, p.clone()],
            vec![],
        );
        let clean_ctor_set_usize = ext(
            mb,
            c,
            "clean_ctor_set_usize",
            vec![p.clone(), Ty::U32, Ty::U64],
            vec![],
        );
        let clean_ctor_set_tag = ext(mb, c, "clean_ctor_set_tag", vec![p.clone(), Ty::U8], vec![]);
        let clean_reset = ext(mb, c, "clean_reset", vec![p.clone()], vec![p.clone()]);
        // Scalar field getters/setters: (obj, byte_offset[:U32]) -> scalar.
        // Names + ScalarWidth order are [U8, U16, U32, U64, F32, F64]; the
        // runtime spells F32 `float32` and F64 `float`.
        let scalar_get = [
            ("clean_ctor_get_uint8", Ty::U8),
            ("clean_ctor_get_uint16", Ty::U16),
            ("clean_ctor_get_uint32", Ty::U32),
            ("clean_ctor_get_uint64", Ty::U64),
            ("clean_ctor_get_float32", Ty::F32),
            ("clean_ctor_get_float", Ty::F64),
        ]
        .map(|(name, ret)| ext(mb, c, name, vec![Ty::Ptr, Ty::U32], vec![ret]));
        let scalar_set = [
            ("clean_ctor_set_uint8", Ty::U8),
            ("clean_ctor_set_uint16", Ty::U16),
            ("clean_ctor_set_uint32", Ty::U32),
            ("clean_ctor_set_uint64", Ty::U64),
            ("clean_ctor_set_float32", Ty::F32),
            ("clean_ctor_set_float", Ty::F64),
        ]
        .map(|(name, val)| ext(mb, c, name, vec![Ty::Ptr, Ty::U32, val], vec![]));
        // Variadic runtime symbols (fixed prefix + trailing pointer args).
        let clean_alloc_ctor = ext_va(
            mb,
            c,
            "clean_alloc_ctor",
            vec![Ty::U32, Ty::U32, Ty::U32],
            vec![p.clone()],
        );
        let clean_reuse = ext_va(
            mb,
            c,
            "clean_reuse",
            vec![p.clone(), Ty::U32, Ty::U32, Ty::U32],
            vec![p.clone()],
        );
        // Canonical `()->()` function type for closure function pointers (a
        // func-type interning does not consume a FuncId, so `c` is untouched).
        let clean_fn_ty = mb.add_func_type(vec![], vec![]);
        let clean_alloc_closure = ext_va(
            mb,
            c,
            "clean_alloc_closure",
            vec![Ty::Func(clean_fn_ty), Ty::U32, Ty::U32],
            vec![p.clone()],
        );
        let mut apply = [clean_inc; 33];
        for (n, slot) in apply.iter_mut().enumerate() {
            let mut params = vec![p.clone()];
            params.extend(std::iter::repeat_n(p.clone(), n));
            *slot = ext(mb, c, &format!("clean_apply_{n}"), params, vec![p.clone()]);
        }
        let clean_apply_n = ext(
            mb,
            c,
            "clean_apply_n",
            vec![p.clone(), Ty::U32, p.clone()],
            vec![p.clone()],
        );
        // String construction from a NUL-terminated C-string global.
        let clean_mk_string = ext(mb, c, "clean_mk_string", vec![p.clone()], vec![p.clone()]);
        Self {
            clean_alloc_ctor,
            clean_box,
            clean_box_uint32,
            clean_box_uint64,
            clean_nat_of_u64,
            clean_nat_big,
            clean_box_float,
            clean_unbox,
            clean_unbox_uint32,
            clean_unbox_uint64,
            clean_unbox_float,
            clean_obj_tag,
            clean_ctor_get,
            clean_ctor_get_usize,
            clean_ctor_set,
            clean_ctor_set_usize,
            clean_ctor_set_tag,
            clean_reset,
            clean_reuse,
            scalar_get,
            scalar_set,
            clean_alloc_closure,
            apply,
            clean_apply_n,
            clean_mk_string,
            clean_fn_ty,
            n_externs: count,
        }
    }

    /// FuncId of the first user-declared function (= number of externs).
    pub(crate) fn next_user_func_index(&self) -> u32 {
        self.n_externs
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
