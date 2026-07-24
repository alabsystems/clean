// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C FFI bindings for clean kernel.
//!
//! This crate exposes a C-compatible API for the clean type checker,
//! enabling use from Python, C, and other languages with minimal overhead.
//!
//! # Memory Management
//!
//! All opaque types must be freed with their corresponding `_free` function.
//! Failure to free results in memory leaks.
//!
//! ## Lifetime Requirements (CRITICAL)
//!
//! **The caller MUST ensure `CleanEnv` outlives all `CleanTypeChecker` instances
//! created from it.** The type checker borrows from the environment - freeing the
//! environment while a type checker exists causes undefined behavior.
//!
//! Correct order:
//! ```text
//! env = clean_env_new()
//! tc = clean_tc_new(env)
//! // ... use tc ...
//! clean_tc_free(tc)    // FREE TC FIRST
//! clean_env_free(env)  // THEN FREE ENV
//! ```
//!
//! Multiple type checkers can be created from the same environment. All must be
//! freed before the environment.
//!
//! # Thread Safety
//!
//! - `CleanEnv` is thread-safe and can be shared across threads (read-only after creation)
//! - `CleanTypeChecker` is NOT thread-safe - create one per thread
//! - `CleanExpr` and `CleanError` are NOT thread-safe - do not share between threads
//!
//! # Error Handling
//!
//! Functions that can fail return NULL and set error via out-parameter.
//! Check the error with `clean_error_message` and free with `clean_error_free`.
//!
//! # Testing
//!
//! For UB detection during development, run tests under Miri:
//! ```text
//! cargo +nightly miri test -p clean-sys
//! ```
//! Note: Miri may not support all FFI patterns.

use clean_kernel::{
    env::Environment,
    expr::{BinderInfo, Expr},
    level::Level,
    tc::TypeChecker,
};
use clean_olean::import::{default_search_paths, load_module_with_deps};
use std::ffi::{c_char, CStr, CString};
use std::path::PathBuf;
use std::ptr;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Opaque environment handle.
pub struct CleanEnv {
    inner: Environment,
    /// Liveness sentinel: `true` while env is alive, set to `false` on free.
    /// Type checkers hold a clone of this Arc to detect use-after-free in debug builds.
    alive: Arc<AtomicBool>,
}

/// Opaque type checker handle.
pub struct CleanTypeChecker<'env> {
    inner: TypeChecker<'env>,
    /// Clone of the parent env's liveness sentinel.
    /// Debug-asserted on every operation to catch use-after-free of the env.
    env_alive: Arc<AtomicBool>,
}

impl CleanTypeChecker<'_> {
    /// Aborts the process if the parent environment has been freed.
    ///
    /// This is a runtime check (not debug-only) because C callers have no
    /// compile-time lifetime enforcement. The cost is a single atomic load.
    ///
    /// Uses `std::process::abort()` instead of `assert!()`/`panic!()` because
    /// this method is called from `extern "C"` functions. Panicking (unwinding)
    /// across an FFI boundary is undefined behavior in Rust when
    /// `panic = "unwind"` (the default for debug builds). `abort()` is always
    /// safe regardless of panic strategy.
    #[inline(always)]
    fn assert_env_alive(&self) {
        if !self.env_alive.load(Ordering::Acquire) {
            std::process::abort();
        }
    }
}

/// Opaque expression handle.
pub struct CleanExpr {
    inner: Expr,
}

/// Opaque error handle.
pub struct CleanError {
    message: CString,
}

// ============================================================================
// Environment Functions
// ============================================================================

/// Create a new empty environment.
///
/// NOTE: Aborts the process on allocation failure (standard Rust OOM behavior).
#[no_mangle]
pub extern "C" fn clean_env_new() -> *mut CleanEnv {
    Box::into_raw(Box::new(CleanEnv {
        inner: Environment::new(),
        alive: Arc::new(AtomicBool::new(true)),
    }))
}

/// Create an environment with the Lean4 Init module loaded.
///
/// If `path` is non-NULL, it is treated as an additional search path for .olean files.
/// If `path` is NULL, only the default search paths are used:
/// 1. `MATHLIB_PATH` environment variable entries (if set)
/// 2. `LEAN_PATH` environment variable entries
/// 3. `~/.elan/toolchains/<version>/lib/lean`
///
/// Returns NULL on error and sets `err_out` if provided.
///
/// # Safety
///
/// If `path` is not NULL, it must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn clean_env_with_init(
    path: *const c_char,
    err_out: *mut *mut CleanError,
) -> *mut CleanEnv {
    let mut search_paths = default_search_paths();

    // Add user-provided path if given
    if !path.is_null() {
        // SAFETY: Caller guarantees path is a valid null-terminated C string.
        let path_str = unsafe { CStr::from_ptr(path) };
        if let Ok(s) = path_str.to_str() {
            search_paths.insert(0, PathBuf::from(s));
        }
    }

    let mut env = Environment::new();

    // Load the Init module
    match load_module_with_deps(&mut env, "Init", &search_paths) {
        Ok(_summaries) => Box::into_raw(Box::new(CleanEnv {
            inner: env,
            alive: Arc::new(AtomicBool::new(true)),
        })),
        Err(e) => {
            if !err_out.is_null() {
                let msg = CString::new(e.to_string()).unwrap_or_default();
                // SAFETY: Caller guarantees err_out is valid (checked non-null above).
                unsafe { *err_out = Box::into_raw(Box::new(CleanError { message: msg })) };
            }
            ptr::null_mut()
        }
    }
}

/// Free an environment.
///
/// # Safety
///
/// `env` must be a valid pointer from `clean_env_new` or NULL.
#[no_mangle]
pub unsafe extern "C" fn clean_env_free(env: *mut CleanEnv) {
    if !env.is_null() {
        // SAFETY: Caller guarantees env is a valid pointer from clean_env_new (checked non-null above).
        let env = unsafe { Box::from_raw(env) };
        // Mark env as dead BEFORE dropping. Any tc that checks after this
        // point will see alive=false and panic in debug builds.
        env.alive.store(false, Ordering::Release);
        drop(env);
    }
}

// ============================================================================
// Type Checker Functions
// ============================================================================

/// Create a new type checker for the given environment.
///
/// The type checker borrows the environment - the environment must outlive
/// the type checker.
///
/// # Safety
///
/// `env` must be a valid pointer to a `CleanEnv`.
#[no_mangle]
pub unsafe extern "C" fn clean_tc_new(env: *const CleanEnv) -> *mut CleanTypeChecker<'static> {
    if env.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: We're creating a TypeChecker that borrows from env.
    // The caller must ensure env outlives the TypeChecker.
    // We use 'static lifetime for the C API - caller is responsible for lifetime.
    let env_ref = unsafe { &(*env).inner };
    let env_alive = unsafe { (*env).alive.clone() };
    let tc = TypeChecker::with_mode(env_ref, env_ref.mode());

    // This is a deliberate lifetime extension for FFI purposes.
    // The C caller is responsible for ensuring env outlives tc.
    let tc_static: TypeChecker<'static> = unsafe { std::mem::transmute(tc) };

    Box::into_raw(Box::new(CleanTypeChecker {
        inner: tc_static,
        env_alive,
    }))
}

/// Free a type checker.
///
/// # Safety
///
/// `tc` must be a valid pointer from `clean_tc_new` or NULL.
#[no_mangle]
pub unsafe extern "C" fn clean_tc_free(tc: *mut CleanTypeChecker) {
    if !tc.is_null() {
        // SAFETY: Caller guarantees tc is from clean_tc_new (checked non-null above).
        drop(unsafe { Box::from_raw(tc) });
    }
}

/// Infer the type of an expression.
///
/// Returns the inferred type, or NULL on error. If `err_out` is not NULL,
/// sets it to the error on failure.
///
/// # Safety
///
/// - `tc` must be a valid pointer to a `CleanTypeChecker`
/// - `expr` must be a valid pointer to a `CleanExpr`
#[no_mangle]
pub unsafe extern "C" fn clean_infer_type(
    tc: *mut CleanTypeChecker,
    expr: *const CleanExpr,
    err_out: *mut *mut CleanError,
) -> *mut CleanExpr {
    if tc.is_null() || expr.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: Caller guarantees tc is valid (checked non-null above).
    let tc_wrapper = unsafe { &mut *tc };
    tc_wrapper.assert_env_alive();
    let tc = &mut tc_wrapper.inner;
    // SAFETY: Caller guarantees expr is valid (checked non-null above).
    let expr = unsafe { &(*expr).inner };

    match tc.infer_type(expr) {
        Ok(ty) => Box::into_raw(Box::new(CleanExpr { inner: ty })),
        Err(e) => {
            if !err_out.is_null() {
                let msg = CString::new(e.to_string()).unwrap_or_default();
                // SAFETY: err_out checked non-null above.
                unsafe { *err_out = Box::into_raw(Box::new(CleanError { message: msg })) };
            }
            ptr::null_mut()
        }
    }
}

/// Check if two expressions are definitionally equal.
///
/// # Safety
///
/// - `tc` must be a valid pointer to a `CleanTypeChecker`
/// - `a` and `b` must be valid pointers to `CleanExpr`
#[no_mangle]
pub unsafe extern "C" fn clean_is_def_eq(
    tc: *mut CleanTypeChecker,
    a: *const CleanExpr,
    b: *const CleanExpr,
) -> bool {
    if tc.is_null() || a.is_null() || b.is_null() {
        return false;
    }

    // SAFETY: Caller guarantees tc, a, b are valid (checked non-null above).
    let tc_wrapper = unsafe { &mut *tc };
    tc_wrapper.assert_env_alive();
    let tc = &mut tc_wrapper.inner;
    let a = unsafe { &(*a).inner };
    let b = unsafe { &(*b).inner };

    tc.is_def_eq(a, b)
}

/// Reduce an expression to weak head normal form.
///
/// Returns the reduced expression. Returns NULL if `tc` or `expr` is NULL.
///
/// # Safety
///
/// If non-NULL, `tc` and `expr` must be valid pointers.
#[no_mangle]
pub unsafe extern "C" fn clean_whnf(
    tc: *mut CleanTypeChecker,
    expr: *const CleanExpr,
) -> *mut CleanExpr {
    if tc.is_null() || expr.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: Caller guarantees tc and expr are valid (checked non-null above).
    // Uses *mut (not *const) because whnf mutates internal RefCell caches,
    // consistent with clean_infer_type and clean_is_def_eq.
    let tc_wrapper = unsafe { &*tc };
    tc_wrapper.assert_env_alive();
    let tc = &tc_wrapper.inner;
    let expr = unsafe { &(*expr).inner };

    let result = tc.whnf(expr);
    Box::into_raw(Box::new(CleanExpr { inner: result }))
}

// ============================================================================
// Expression Construction
// ============================================================================

/// Create a constant expression from a name string.
///
/// # Safety
///
/// `name` must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn clean_expr_const(name: *const c_char) -> *mut CleanExpr {
    if name.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: Caller guarantees name is a valid null-terminated C string (checked non-null above).
    let name_str = unsafe { CStr::from_ptr(name) };
    let name_str = match name_str.to_str() {
        Ok(s) => s,
        Err(_) => return ptr::null_mut(),
    };

    let expr = Expr::const_str(name_str);
    Box::into_raw(Box::new(CleanExpr { inner: expr }))
}

/// Create an application expression: `f a`.
///
/// # Safety
///
/// `f` and `a` must be valid pointers to `CleanExpr`.
#[no_mangle]
pub unsafe extern "C" fn clean_expr_app(
    f: *const CleanExpr,
    a: *const CleanExpr,
) -> *mut CleanExpr {
    if f.is_null() || a.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: Caller guarantees f and a are valid (checked non-null above).
    let f = unsafe { (*f).inner.clone() };
    let a = unsafe { (*a).inner.clone() };

    let expr = Expr::app(f, a);
    Box::into_raw(Box::new(CleanExpr { inner: expr }))
}

/// Create a lambda expression: `λ x : ty. body`.
///
/// The body should use BVar(0) to refer to the bound variable.
///
/// # Safety
///
/// `ty` and `body` must be valid pointers to `CleanExpr`.
#[no_mangle]
pub unsafe extern "C" fn clean_expr_lam(
    ty: *const CleanExpr,
    body: *const CleanExpr,
) -> *mut CleanExpr {
    if ty.is_null() || body.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: Caller guarantees ty and body are valid (checked non-null above).
    let ty = unsafe { (*ty).inner.clone() };
    let body = unsafe { (*body).inner.clone() };

    let expr = Expr::lam(BinderInfo::Default, ty, body);
    Box::into_raw(Box::new(CleanExpr { inner: expr }))
}

/// Create a pi (forall) expression: `∀ x : ty. body`.
///
/// The body should use BVar(0) to refer to the bound variable.
///
/// # Safety
///
/// `ty` and `body` must be valid pointers to `CleanExpr`.
#[no_mangle]
pub unsafe extern "C" fn clean_expr_pi(
    ty: *const CleanExpr,
    body: *const CleanExpr,
) -> *mut CleanExpr {
    if ty.is_null() || body.is_null() {
        return ptr::null_mut();
    }

    // SAFETY: Caller guarantees ty and body are valid (checked non-null above).
    let ty = unsafe { (*ty).inner.clone() };
    let body = unsafe { (*body).inner.clone() };

    let expr = Expr::pi(BinderInfo::Default, ty, body);
    Box::into_raw(Box::new(CleanExpr { inner: expr }))
}

/// Create a natural number literal expression.
#[no_mangle]
pub extern "C" fn clean_expr_nat(n: u64) -> *mut CleanExpr {
    let expr = Expr::nat_lit(n);
    Box::into_raw(Box::new(CleanExpr { inner: expr }))
}

/// Create the Prop sort expression (Sort 0).
#[no_mangle]
pub extern "C" fn clean_expr_prop() -> *mut CleanExpr {
    Box::into_raw(Box::new(CleanExpr {
        inner: Expr::prop(),
    }))
}

/// Create the Type sort expression (Sort 1).
#[no_mangle]
pub extern "C" fn clean_expr_type() -> *mut CleanExpr {
    Box::into_raw(Box::new(CleanExpr {
        inner: Expr::type_(),
    }))
}

/// Create a Sort expression at the given level.
#[no_mangle]
pub extern "C" fn clean_expr_sort(level: u32) -> *mut CleanExpr {
    let mut l = Level::zero();
    for _ in 0..level {
        l = Level::succ(l);
    }
    Box::into_raw(Box::new(CleanExpr {
        inner: Expr::sort(l),
    }))
}

/// Create a bound variable expression.
///
/// De Bruijn index 0 refers to the innermost binder.
#[no_mangle]
pub extern "C" fn clean_expr_bvar(idx: u32) -> *mut CleanExpr {
    Box::into_raw(Box::new(CleanExpr {
        inner: Expr::bvar(idx),
    }))
}

/// Free an expression.
///
/// # Safety
///
/// `expr` must be a valid pointer from an expression constructor or NULL.
#[no_mangle]
pub unsafe extern "C" fn clean_expr_free(expr: *mut CleanExpr) {
    if !expr.is_null() {
        // SAFETY: Caller guarantees expr is from an expression constructor (checked non-null above).
        drop(unsafe { Box::from_raw(expr) });
    }
}

// ============================================================================
// Error Handling
// ============================================================================

/// Get the error message as a C string.
///
/// The returned pointer is valid until `clean_error_free` is called.
///
/// # Safety
///
/// `err` must be a valid pointer to a `CleanError`.
#[no_mangle]
pub unsafe extern "C" fn clean_error_message(err: *const CleanError) -> *const c_char {
    if err.is_null() {
        return ptr::null();
    }

    // SAFETY: Caller guarantees err is valid (checked non-null above).
    unsafe { (*err).message.as_ptr() }
}

/// Free an error.
///
/// # Safety
///
/// `err` must be a valid pointer from error output or NULL.
#[no_mangle]
pub unsafe extern "C" fn clean_error_free(err: *mut CleanError) {
    if !err.is_null() {
        // SAFETY: Caller guarantees err is from error output (checked non-null above).
        drop(unsafe { Box::from_raw(err) });
    }
}

// ============================================================================
// Utility Functions
// ============================================================================

/// Get the version string of the clean library.
///
/// Returns the Cargo package version (from `CARGO_PKG_VERSION`).
#[no_mangle]
pub extern "C" fn clean_version() -> *const c_char {
    static VERSION: &[u8] = concat!(env!("CARGO_PKG_VERSION"), "\0").as_bytes();
    VERSION.as_ptr() as *const c_char
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_use_after_free_guard(tc: *mut CleanTypeChecker, api_name: &str) {
        // SAFETY: Tests pass valid pointers returned by `clean_tc_new`.
        let tc_ref = unsafe { &*tc };

        // Verify the sentinel is false after env_free. This is the same check
        // that `assert_env_alive()` performs — if the sentinel is false, the
        // production code will abort the process. We verify the sentinel directly
        // rather than calling `assert_env_alive()` because it now uses
        // `std::process::abort()` (not panic), which cannot be caught.
        assert!(
            !tc_ref.env_alive.load(Ordering::Acquire),
            "env_alive should be false after env_free ({api_name})"
        );
    }

    fn leak_tc_after_env_free(tc: *mut CleanTypeChecker) {
        // SAFETY: In wrong-lifecycle tests the env has already been freed.
        // Dropping TypeChecker would touch a dangling env borrow, so intentionally
        // leak this one allocation to keep the test defined.
        unsafe {
            std::mem::forget(Box::from_raw(tc));
        }
    }

    #[test]
    fn test_env_lifecycle() {
        let env = clean_env_new();
        assert!(!env.is_null());
        unsafe { clean_env_free(env) };
    }

    #[test]
    fn test_tc_lifecycle() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };
        assert!(!tc.is_null());
        unsafe {
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }

    #[test]
    fn test_expr_prop() {
        let prop = clean_expr_prop();
        assert!(!prop.is_null());
        unsafe { clean_expr_free(prop) };
    }

    #[test]
    fn test_infer_type_prop() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };
        let prop = clean_expr_prop();

        let mut err: *mut CleanError = ptr::null_mut();
        let ty = unsafe { clean_infer_type(tc, prop, &mut err) };

        assert!(!ty.is_null());
        assert!(err.is_null());

        unsafe {
            clean_expr_free(ty);
            clean_expr_free(prop);
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }

    #[test]
    fn test_is_def_eq() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };
        let prop1 = clean_expr_prop();
        let prop2 = clean_expr_prop();

        let eq = unsafe { clean_is_def_eq(tc, prop1, prop2) };
        assert!(eq);

        unsafe {
            clean_expr_free(prop1);
            clean_expr_free(prop2);
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }

    // Gated: hangs at _dyld_start on macOS (#2950)
    #[cfg(feature = "ffi-tests")]
    #[test]
    fn test_env_with_init() {
        // Test with NULL path - uses default search paths
        let mut err: *mut CleanError = ptr::null_mut();
        let env = unsafe { clean_env_with_init(ptr::null(), &mut err) };

        if env.is_null() {
            // If Init not found, check error was set
            if !err.is_null() {
                let msg = unsafe { CStr::from_ptr(clean_error_message(err)) };
                eprintln!("clean_env_with_init error: {:?}", msg);
                unsafe { clean_error_free(err) };
            }
            // Skip test if Init module not available
            return;
        }

        assert!(err.is_null());

        // Create type checker and verify it works
        let tc = unsafe { clean_tc_new(env) };
        assert!(!tc.is_null());

        // Test Nat.zero lookup
        let nat_zero = unsafe { clean_expr_const(c"Nat.zero".as_ptr()) };
        let mut infer_err: *mut CleanError = ptr::null_mut();
        let ty = unsafe { clean_infer_type(tc, nat_zero, &mut infer_err) };

        // Type should be Nat (from Init)
        if !ty.is_null() {
            unsafe { clean_expr_free(ty) };
        }

        unsafe {
            clean_expr_free(nat_zero);
            clean_tc_free(tc);
            clean_env_free(env);
            if !infer_err.is_null() {
                clean_error_free(infer_err);
            }
        }
    }

    // ========================================================================
    // FFI Safety Tests (#450)
    // ========================================================================

    /// Test that NULL pointers are handled gracefully by all functions.
    // Gated: hangs at _dyld_start on macOS (#2950)
    #[cfg(feature = "ffi-tests")]
    #[test]
    fn test_null_pointer_handling() {
        // clean_env_free(NULL) - should not crash
        unsafe { clean_env_free(ptr::null_mut()) };

        // clean_tc_new(NULL) - should return NULL
        let tc = unsafe { clean_tc_new(ptr::null()) };
        assert!(tc.is_null());

        // clean_tc_free(NULL) - should not crash
        unsafe { clean_tc_free(ptr::null_mut()) };

        // clean_expr_free(NULL) - should not crash
        unsafe { clean_expr_free(ptr::null_mut()) };

        // clean_error_free(NULL) - should not crash
        unsafe { clean_error_free(ptr::null_mut()) };

        // clean_error_message(NULL) - should return NULL
        let msg = unsafe { clean_error_message(ptr::null()) };
        assert!(msg.is_null());

        // clean_expr_const(NULL) - should return NULL
        let expr = unsafe { clean_expr_const(ptr::null()) };
        assert!(expr.is_null());

        // clean_expr_app(NULL, NULL) - should return NULL
        let app = unsafe { clean_expr_app(ptr::null(), ptr::null()) };
        assert!(app.is_null());

        // clean_expr_lam(NULL, NULL) - should return NULL
        let lam = unsafe { clean_expr_lam(ptr::null(), ptr::null()) };
        assert!(lam.is_null());

        // clean_expr_pi(NULL, NULL) - should return NULL
        let pi = unsafe { clean_expr_pi(ptr::null(), ptr::null()) };
        assert!(pi.is_null());

        // clean_infer_type(NULL, NULL, NULL) - should return NULL
        let ty = unsafe { clean_infer_type(ptr::null_mut(), ptr::null(), ptr::null_mut()) };
        assert!(ty.is_null());

        // clean_is_def_eq(NULL, NULL, NULL) - should return false
        let eq = unsafe { clean_is_def_eq(ptr::null_mut(), ptr::null(), ptr::null()) };
        assert!(!eq);

        // clean_whnf(NULL, NULL) - should return NULL
        let whnf = unsafe { clean_whnf(ptr::null_mut(), ptr::null()) };
        assert!(whnf.is_null());

        // clean_env_with_init(NULL, NULL) - should handle gracefully
        // (may fail due to Init not found, but should not crash)
        let env = unsafe { clean_env_with_init(ptr::null(), ptr::null_mut()) };
        if !env.is_null() {
            unsafe { clean_env_free(env) };
        }
    }

    /// Test that partial NULL arguments are handled correctly.
    #[test]
    fn test_partial_null_args() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };
        let prop = clean_expr_prop();

        // clean_expr_app with one NULL
        let app1 = unsafe { clean_expr_app(prop, ptr::null()) };
        assert!(app1.is_null());
        let app2 = unsafe { clean_expr_app(ptr::null(), prop) };
        assert!(app2.is_null());

        // clean_infer_type with NULL tc
        let mut err: *mut CleanError = ptr::null_mut();
        let ty = unsafe { clean_infer_type(ptr::null_mut(), prop, &mut err) };
        assert!(ty.is_null());

        // clean_infer_type with NULL expr
        let ty2 = unsafe { clean_infer_type(tc, ptr::null(), &mut err) };
        assert!(ty2.is_null());

        // clean_is_def_eq with one NULL expr
        let eq1 = unsafe { clean_is_def_eq(tc, prop, ptr::null()) };
        assert!(!eq1);
        let eq2 = unsafe { clean_is_def_eq(tc, ptr::null(), prop) };
        assert!(!eq2);

        unsafe {
            clean_expr_free(prop);
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }

    /// Test correct lifecycle ordering: tc MUST be freed before env.
    /// This test documents the expected usage pattern.
    #[test]
    fn test_correct_lifecycle_order() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        // Use the type checker
        let prop = clean_expr_prop();
        let mut err: *mut CleanError = ptr::null_mut();
        let ty = unsafe { clean_infer_type(tc, prop, &mut err) };
        assert!(!ty.is_null());

        // CORRECT ORDER: free tc first, then env
        unsafe {
            clean_expr_free(ty);
            clean_expr_free(prop);
            clean_tc_free(tc); // tc freed first
            clean_env_free(env); // env freed second
        }
    }

    /// Test that freeing env sets the liveness sentinel to false (#1339).
    ///
    /// Previous tests used `catch_unwind` around `extern "C"` FFI calls, which is
    /// UB (panicking across FFI aborts the process). Instead, we verify the
    /// `env_alive` sentinel directly — the same mechanism that `assert_env_alive()`
    /// checks via `debug_assert!` on every FFI operation.
    #[test]
    fn test_wrong_lifecycle_order_detected() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        // Before freeing: sentinel should be true
        let tc_ref = unsafe { &*tc };
        assert!(
            tc_ref.env_alive.load(Ordering::Acquire),
            "env_alive should be true before env_free"
        );

        // WRONG ORDER: free env first (tc still alive)
        unsafe { clean_env_free(env) };

        assert_use_after_free_guard(tc, "infer_type");

        leak_tc_after_env_free(tc);
    }

    /// Test that is_def_eq sentinel works after env free (#1339).
    #[test]
    fn test_wrong_lifecycle_is_def_eq_detected() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        // Free env first (wrong order)
        unsafe { clean_env_free(env) };

        assert_use_after_free_guard(tc, "is_def_eq");

        leak_tc_after_env_free(tc);
    }

    /// Test that whnf sentinel works after env free (#1339).
    #[test]
    fn test_wrong_lifecycle_whnf_detected() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        // Free env first (wrong order)
        unsafe { clean_env_free(env) };

        assert_use_after_free_guard(tc, "whnf");

        leak_tc_after_env_free(tc);
    }

    /// Test multiple type checkers from the same environment.
    /// Each type checker is independent.
    #[test]
    fn test_multiple_type_checkers() {
        let env = clean_env_new();

        // Create two type checkers from the same env
        let tc1 = unsafe { clean_tc_new(env) };
        let tc2 = unsafe { clean_tc_new(env) };
        assert!(!tc1.is_null());
        assert!(!tc2.is_null());

        // Both should work independently
        let prop1 = clean_expr_prop();
        let prop2 = clean_expr_prop();

        let mut err1: *mut CleanError = ptr::null_mut();
        let mut err2: *mut CleanError = ptr::null_mut();

        let ty1 = unsafe { clean_infer_type(tc1, prop1, &mut err1) };
        let ty2 = unsafe { clean_infer_type(tc2, prop2, &mut err2) };

        assert!(!ty1.is_null());
        assert!(!ty2.is_null());

        // Free in correct order: all type checkers before env
        unsafe {
            clean_expr_free(ty1);
            clean_expr_free(ty2);
            clean_expr_free(prop1);
            clean_expr_free(prop2);
            clean_tc_free(tc1);
            clean_tc_free(tc2);
            clean_env_free(env);
        }
    }

    /// Test that expressions can be used across type checker boundaries.
    /// An expression created with one tc can be checked by another.
    #[test]
    fn test_expr_independence() {
        let env = clean_env_new();
        let tc1 = unsafe { clean_tc_new(env) };
        let tc2 = unsafe { clean_tc_new(env) };

        // Create expression using tc1
        let prop = clean_expr_prop();
        let mut err: *mut CleanError = ptr::null_mut();
        let ty1 = unsafe { clean_infer_type(tc1, prop, &mut err) };
        assert!(!ty1.is_null());

        // Same expression should work with tc2
        let ty2 = unsafe { clean_infer_type(tc2, prop, &mut err) };
        assert!(!ty2.is_null());

        // They should be definitionally equal
        let eq = unsafe { clean_is_def_eq(tc1, ty1, ty2) };
        assert!(eq);

        unsafe {
            clean_expr_free(ty1);
            clean_expr_free(ty2);
            clean_expr_free(prop);
            clean_tc_free(tc1);
            clean_tc_free(tc2);
            clean_env_free(env);
        }
    }

    /// Test error handling: infer_type should set error on failure.
    #[test]
    fn test_error_on_invalid_expr() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        // Create an invalid expression: application of non-function
        // Prop : Type, so `Prop Prop` is type error
        let prop = clean_expr_prop();
        let bad_app = unsafe { clean_expr_app(prop, prop) };

        let mut err: *mut CleanError = ptr::null_mut();
        let ty = unsafe { clean_infer_type(tc, bad_app, &mut err) };

        // Should fail and set error
        assert!(ty.is_null());
        assert!(!err.is_null());

        // Error message should be non-empty
        let msg = unsafe { clean_error_message(err) };
        assert!(!msg.is_null());
        let msg_str = unsafe { CStr::from_ptr(msg) };
        assert!(
            !msg_str.to_bytes().is_empty(),
            "Error message should not be empty"
        );

        unsafe {
            clean_error_free(err);
            clean_expr_free(bad_app);
            clean_expr_free(prop);
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }

    /// Test whnf with valid inputs.
    #[test]
    fn test_whnf_valid_input() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        let _: unsafe extern "C" fn(*mut _, *const _) -> *mut _ = clean_whnf;
        let prop = clean_expr_prop();
        let reduced = unsafe { clean_whnf(tc, prop) };
        assert!(!reduced.is_null());

        // The reduced form should be definitionally equal to the original
        let eq = unsafe { clean_is_def_eq(tc, prop, reduced) };
        assert!(eq);

        unsafe {
            clean_expr_free(reduced);
            clean_expr_free(prop);
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }

    /// Test version function returns valid semver string.
    #[test]
    fn test_version() {
        let version = clean_version();
        assert!(!version.is_null());
        let version_str = unsafe { CStr::from_ptr(version) };
        let version_bytes = version_str.to_bytes();
        assert!(!version_bytes.is_empty());
        // Verify semver format (major.minor.patch)
        let version = std::str::from_utf8(version_bytes).expect("version should be UTF-8");
        let parts: Vec<&str> = version.split('.').collect();
        assert!(
            parts.len() >= 2,
            "version '{}' should have at least major.minor",
            version
        );
        for part in &parts {
            // Each part should be numeric (possibly with -suffix for pre-release)
            let numeric_part = part.split('-').next().unwrap();
            assert!(
                numeric_part.chars().all(|c| c.is_ascii_digit()),
                "version part '{}' should be numeric",
                part
            );
        }
    }

    /// Test all expression constructors produce valid expressions.
    #[test]
    fn test_all_expr_constructors() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        // Test each constructor
        let prop = clean_expr_prop();
        let type_ = clean_expr_type();
        let sort = clean_expr_sort(2);
        let nat = clean_expr_nat(42);
        let bvar = clean_expr_bvar(0);

        // All should be non-null
        assert!(!prop.is_null());
        assert!(!type_.is_null());
        assert!(!sort.is_null());
        assert!(!nat.is_null());
        assert!(!bvar.is_null());

        // Prop, Type, Sort should have inferable types
        let mut err: *mut CleanError = ptr::null_mut();

        let prop_ty = unsafe { clean_infer_type(tc, prop, &mut err) };
        assert!(!prop_ty.is_null());

        let type_ty = unsafe { clean_infer_type(tc, type_, &mut err) };
        assert!(!type_ty.is_null());

        let sort_ty = unsafe { clean_infer_type(tc, sort, &mut err) };
        assert!(!sort_ty.is_null());

        // Nat literal type inference depends on Nat being defined
        // BVar type inference requires it to be bound

        unsafe {
            clean_expr_free(prop_ty);
            clean_expr_free(type_ty);
            clean_expr_free(sort_ty);
            clean_expr_free(prop);
            clean_expr_free(type_);
            clean_expr_free(sort);
            clean_expr_free(nat);
            clean_expr_free(bvar);
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }

    /// Test lambda and pi expression construction.
    #[test]
    fn test_lambda_pi_construction() {
        let env = clean_env_new();
        let tc = unsafe { clean_tc_new(env) };

        let prop = clean_expr_prop();
        let bvar = clean_expr_bvar(0);

        // λ _ : Prop. #0 (identity on Prop)
        let lam = unsafe { clean_expr_lam(prop, bvar) };
        assert!(!lam.is_null());

        // ∀ _ : Prop. #0 (type of Prop identity)
        let prop2 = clean_expr_prop();
        let bvar2 = clean_expr_bvar(0);
        let pi = unsafe { clean_expr_pi(prop2, bvar2) };
        assert!(!pi.is_null());

        // Lambda should have a Pi type
        let mut err: *mut CleanError = ptr::null_mut();
        let lam_ty = unsafe { clean_infer_type(tc, lam, &mut err) };
        assert!(!lam_ty.is_null());

        unsafe {
            clean_expr_free(lam_ty);
            clean_expr_free(lam);
            clean_expr_free(pi);
            clean_expr_free(prop);
            clean_expr_free(prop2);
            clean_expr_free(bvar);
            clean_expr_free(bvar2);
            clean_tc_free(tc);
            clean_env_free(env);
        }
    }
}
