// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Micro-checker core: certificate verification engine.
//!
//! # Env-aware diversity (the #3 increment)
//!
//! The checker now consults a read-only [`MicroEnv`] so it can resolve
//! `Const` references (their TYPES, and — for reducible defs — their BODIES).
//! This unblocks the `:= rfl` corpus: those proofs reduce named definitions
//! via DELTA (constant unfolding) + IOTA (native Nat/Bool reductions), so a
//! checker with NO environment could only ever verify closed pure-λ terms.
//!
//! Crucially the checker still uses its OWN [`whnf_impl`] / [`def_eq_impl`] /
//! [`native`](super::native) arithmetic. The env is JUST a name→(type,body)
//! table; the reduction engine is wholly separate from the kernel's
//! `whnf`/`is_def_eq`. That separation is the entire diversity value.
//!
//! Any construct the checker cannot model (an unknown const, an irreducible
//! const stuck under an op, a recursor outside the native Nat/Bool set, …) is
//! surfaced as [`MicroResult::Unsupported`] — a HARD failure for the gate,
//! never a silent skip.

use std::sync::Arc;

use num_traits::Zero;

use crate::expr::stack_safe;

use super::env::MicroEnv;
use super::types::{MicroCert, MicroError, MicroExpr, MicroLevel, MicroLiteral, MicroResult};

/// A shared empty env, used by the env-less back-compat constructor.
static EMPTY_ENV: std::sync::LazyLock<MicroEnv> = std::sync::LazyLock::new(MicroEnv::new);

/// Whether a const name is a native op kept OPAQUE to delta — only the
/// native rule (or recursor IOTA) reduces it. Covers the native Nat ops
/// (`native::reduce_nat_app`), `Nat.succ`, and the native Bool ops
/// (`native::reduce_bool_app`, e.g. `Bool.beq`). Keeping these opaque ensures
/// the spine's IOTA-first path fires the micro-checker's OWN rule rather than
/// delta-unfolding into the prelude's `*.rec` body.
fn is_native_op(name: &str) -> bool {
    super::native::NAT_BINOPS.contains(&name)
        || name == "Nat.succ"
        || super::native::BOOL_BINOPS.contains(&name)
}

/// The structural recursors the micro-checker models with its OWN IOTA engine
/// (see [`MicroChecker::reduce_recursor`]). A CLOSED allowlist: any other
/// `*.rec` head stays stuck and the gate fails closed (`Unsupported`).
///
/// `Bool.rec` is the high-value one — the prelude's `Bool.and`/`Bool.or`/
/// `Bool.xor`/`Bool.not` and the `if (c : Bool) then _ else _` (`cond`) form
/// all reduce through it. `Nat.rec` is the structural Nat eliminator (zero /
/// succ casework), included for principled completeness.
const RECURSORS: &[&str] = &["Bool.rec", "Nat.rec"];

/// If `e` (a normal form) is NOT a closed value — i.e. it is, or is headed by,
/// a `Const` that is neither a recognised Nat value constructor nor a literal —
/// return that stuck head's name. A closed value is a `Nat` literal, or a
/// `Nat.zero` / `Nat.succ <value>` chain. Anything else with a `Const` head
/// (a stuck native op left un-reduced, a `*.rec` recursor we don't model, an
/// unfoldable definition) is "stuck on an unmodelable construct".
fn stuck_head(e: &MicroExpr) -> Option<String> {
    stack_safe(|| stuck_head_impl(e))
}

fn stuck_head_impl(e: &MicroExpr) -> Option<String> {
    match e {
        MicroExpr::Lit(_) => None,
        MicroExpr::Const(name) => {
            // Closed value constructors: `Nat.zero` and the two `Bool` ctors.
            // (`Bool.true`/`Bool.false` are the values the NZCV-flag / `topSet`
            // theorems reduce to once `Bool.rec` IOTA fires.)
            if matches!(&**name, "Nat.zero" | "Bool.true" | "Bool.false") {
                None
            } else {
                Some(name.to_string())
            }
        }
        MicroExpr::App(f, a) => {
            // Allow the `Nat.succ <value>` constructor chain.
            let head = app_head(e);
            if let MicroExpr::Const(name) = head {
                if &**name == "Nat.succ" {
                    return stuck_head(a);
                }
                return Some(name.to_string());
            }
            stuck_head(f).or_else(|| stuck_head(a))
        }
        // A bare lambda/Pi/sort as the "value" of a Nat computation is itself
        // a sign the reduction did not produce a value.
        MicroExpr::Lam(..) | MicroExpr::Pi(..) | MicroExpr::Let(..) => {
            Some("<non-value: binder>".to_string())
        }
        MicroExpr::BVar(_) | MicroExpr::Sort(_) | MicroExpr::Opaque(_) | MicroExpr::Proj(..) => {
            None
        }
    }
}

/// The head of an application spine.
fn app_head(e: &MicroExpr) -> &MicroExpr {
    let mut h = e;
    while let MicroExpr::App(f, _) = h {
        h = f;
    }
    h
}

/// A `Nat` major premise recognised in constructor form (for `Nat.rec` IOTA).
enum NatCtor {
    /// `Nat.zero` (or the literal `0`).
    Zero,
    /// `Nat.succ <pred>` — the predecessor MicroExpr (a literal for `n > 0`).
    Succ(MicroExpr),
}

/// Recognise a fully-reduced `MicroExpr` as a `Nat` constructor for `Nat.rec`.
///
/// A `Nat` literal `n` is its own constructor view: `0` is `Zero`, and `n > 0`
/// is `Succ(n-1)` (the predecessor as a literal — matching the kernel's lazy
/// literal/constructor bridge). The explicit `Nat.zero` const and a
/// `Nat.succ <x>` application are also recognised. Anything else -> `None`
/// (the recursor stays stuck and the gate fails closed).
fn nat_constructor(e: &MicroExpr) -> Option<NatCtor> {
    match e {
        MicroExpr::Lit(MicroLiteral::Nat(n)) => {
            if n.is_zero() {
                Some(NatCtor::Zero)
            } else {
                Some(NatCtor::Succ(MicroExpr::Lit(MicroLiteral::Nat(n - 1u32))))
            }
        }
        MicroExpr::Const(name) if &**name == "Nat.zero" => Some(NatCtor::Zero),
        MicroExpr::App(f, a) => match &**f {
            MicroExpr::Const(name) if &**name == "Nat.succ" => {
                Some(NatCtor::Succ(a.as_ref().clone()))
            }
            _ => None,
        },
        _ => None,
    }
}

// ============================================================================
// Micro-Checker Core
// ============================================================================

/// Minimal certificate checker state, parameterised by a read-only env.
pub struct MicroChecker<'env> {
    /// Type context (de Bruijn levels: index 0 = outermost binding)
    context: Vec<MicroExpr>,
    /// Read-only constant table (delta + Const typing). Borrowed, never mutated.
    env: &'env MicroEnv,
    /// Fuel for the reducer, to keep WHNF terminating on pathological input.
    /// Decremented per reduction step; hitting zero yields `Unsupported`.
    fuel: std::cell::Cell<u64>,
    /// Universe-blind typing: treat any two `Sort` levels as equal.
    ///
    /// The env-aware diversity gate erases universe levels (the targeted
    /// `:= rfl` corpus is monomorphic but its standard `Eq.{u}` / `Eq.refl.{u}`
    /// heads carry a universe PARAMETER). Re-deriving universe instantiation
    /// would mean re-implementing universe inference; instead the env-aware
    /// checker runs universe-BLIND for typing. This only makes the TYPING half
    /// weaker (it can never reject a true theorem); the LOAD-BEARING half is
    /// the independent reduction re-check (`check_def_eq_result`), which is
    /// universe-independent and catches any false `rfl`. The env-less
    /// back-compat checker stays universe-strict.
    universe_blind: bool,
}

/// Default reduction fuel. The corpus reduces a handful of 64-bit ops per
/// theorem; a generous bound that still guarantees termination.
const DEFAULT_FUEL: u64 = 5_000_000;

impl<'env> MicroChecker<'env> {
    /// Create a new env-less micro-checker (back-compat).
    ///
    /// With no environment, every `Const` resolves to `Unsupported`. Suitable
    /// only for closed pure-λ terms. Prefer [`Self::with_env`] for the
    /// diversity gate.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns a fresh MicroChecker with empty context and empty env.
    pub fn new() -> MicroChecker<'static> {
        MicroChecker {
            context: Vec::new(),
            env: &EMPTY_ENV,
            fuel: std::cell::Cell::new(DEFAULT_FUEL),
            universe_blind: false,
        }
    }

    /// Create an env-aware micro-checker over a read-only [`MicroEnv`].
    ///
    /// Runs universe-blind for typing (see [`Self::universe_blind`]). The
    /// load-bearing reduction re-check is universe-independent.
    pub fn with_env(env: &'env MicroEnv) -> Self {
        MicroChecker {
            context: Vec::new(),
            env,
            fuel: std::cell::Cell::new(DEFAULT_FUEL),
            universe_blind: true,
        }
    }

    /// Verify a certificate against an expression, returning the proven type.
    ///
    /// Back-compat shape: returns `Err` for both genuine rejection and
    /// (env-less) unsupported constructs. Prefer [`Self::verify_result`] for
    /// the diversity gate, which distinguishes `Unsupported` (fail-closed)
    /// from `Rejected`.
    pub fn verify(&mut self, cert: &MicroCert, expr: &MicroExpr) -> Result<MicroExpr, MicroError> {
        self.fuel.set(DEFAULT_FUEL);
        stack_safe(|| self.verify_impl(cert, expr))
    }

    /// Verify a certificate, distinguishing `Verified` / `Rejected` /
    /// `Unsupported`. This is the env-aware entry point for the diversity gate.
    pub fn verify_result(&mut self, cert: &MicroCert, expr: &MicroExpr) -> MicroResult {
        self.fuel.set(DEFAULT_FUEL);
        match stack_safe(|| self.verify_impl(cert, expr)) {
            Ok(ty) => MicroResult::Verified(ty),
            Err(MicroError::Unsupported(msg)) => MicroResult::Unsupported(msg),
            Err(e) => MicroResult::Rejected(e),
        }
    }

    /// Independently re-check, via the micro-checker's OWN reducer, that two
    /// expressions are definitionally equal (delta + iota + beta + zeta).
    ///
    /// This is the load-bearing diversity check for a `:= rfl` theorem: the
    /// kernel accepts `rfl : lhs = rhs` only because `lhs ≡ rhs`; this method
    /// re-derives that equality with a second, independently-written
    /// normalizer. Returns `Unsupported` if either side gets stuck on a
    /// construct the checker cannot model (fail-closed), `Verified` of `lhs`
    /// if they reduce equal, `Rejected` if they reduce to distinct normal
    /// forms.
    ///
    /// `require_value`: when `true` (the rfl REDUCTION stage), each normal form
    /// MUST be a fully-evaluated closed value (a Nat literal or a constructor
    /// chain). If a side gets STUCK on an unmodelable head (e.g. a `Nat.rec`
    /// the micro-checker does not implement), the result is `Unsupported`
    /// (fail-closed) rather than a misleading `Rejected`. When `false` (the
    /// TYPE-comparison stage) stuck spines are expected (types are not values)
    /// and only structural inequality is a `Rejected`.
    pub fn check_def_eq_result(&self, lhs: &MicroExpr, rhs: &MicroExpr) -> MicroResult {
        self.check_eq_inner(lhs, rhs, false)
    }

    /// As [`check_def_eq_result`] but requires both normal forms to be closed
    /// values — used for the rfl reduction stage so an unmodelable recursor
    /// FAILS CLOSED as `Unsupported`.
    pub fn check_value_eq_result(&self, lhs: &MicroExpr, rhs: &MicroExpr) -> MicroResult {
        self.check_eq_inner(lhs, rhs, true)
    }

    fn check_eq_inner(&self, lhs: &MicroExpr, rhs: &MicroExpr, require_value: bool) -> MicroResult {
        self.fuel.set(DEFAULT_FUEL);
        let a = stack_safe(|| self.whnf_full(lhs));
        let b = stack_safe(|| self.whnf_full(rhs));
        match (a, b) {
            (Ok(an), Ok(bn)) => {
                if require_value {
                    if let Some(stuck) = stuck_head(&an).or_else(|| stuck_head(&bn)) {
                        return MicroResult::Unsupported(format!(
                            "rfl reduction stuck on unmodelable head `{stuck}` \
                             (not a closed value) — fail-closed"
                        ));
                    }
                }
                if self.structural_eq_impl(&an, &bn) {
                    MicroResult::Verified(an)
                } else {
                    MicroResult::Rejected(MicroError::TypeMismatch {
                        expected: bn,
                        actual: an,
                    })
                }
            }
            (Err(m), _) | (_, Err(m)) => match m {
                MicroError::Unsupported(s) => MicroResult::Unsupported(s),
                other => MicroResult::Unsupported(other.to_string()),
            },
        }
    }

    #[cfg(any(test, kani))]
    pub(crate) fn context_depth(&self) -> usize {
        self.context.len()
    }

    /// Re-enter the stack guard for every recursive certificate descent.
    ///
    /// The public entry points guard their first call, but a single
    /// `stacker::maybe_grow` segment is finite. Deep Pi/Lam/App/Let
    /// certificates must therefore cross this boundary again at each child;
    /// recursing straight into `verify_impl` eventually exhausts the grown
    /// segment on an ordinary Rust test-thread stack.
    #[inline(always)]
    fn verify_recurse(
        &mut self,
        cert: &MicroCert,
        expr: &MicroExpr,
    ) -> Result<MicroExpr, MicroError> {
        stack_safe(|| self.verify_impl(cert, expr))
    }

    /// Implementation of certificate verification.
    ///
    /// Every recursive edge goes through [`Self::verify_recurse`].
    fn verify_impl(&mut self, cert: &MicroCert, expr: &MicroExpr) -> Result<MicroExpr, MicroError> {
        match (cert, expr) {
            // Sort rule: Sort(l) : Sort(succ(l))
            (MicroCert::Sort { level }, MicroExpr::Sort(l)) => {
                if !level.level_eq(l) {
                    return Err(MicroError::LevelMismatch {
                        expected: level.clone(),
                        actual: l.clone(),
                    });
                }
                Ok(MicroExpr::Sort(MicroLevel::succ(level.clone())))
            }

            // Const rule: resolve type from env, cross-check cert-carried type.
            (MicroCert::Const { name, ty }, MicroExpr::Const(n)) => {
                if name != n {
                    return Err(MicroError::StructureMismatch);
                }
                // Fail-closed coverage check: the const MUST be modeled by the
                // read-only env, else we cannot vouch for it.
                if self.env.get(name).is_none() {
                    return Err(MicroError::Unsupported(format!(
                        "Const {name:?} not in micro-env (cannot resolve)"
                    )));
                }
                // Return the cert-carried INSTANTIATED type. We do not re-derive
                // universe instantiation here (levels are intentionally erased
                // for the monomorphic corpus); the diversity value lives in the
                // App-rule type recomputation and the independent reduction
                // re-check, both of which use this type. The env-presence gate
                // above is what keeps this fail-closed.
                Ok(ty.as_ref().clone())
            }

            // BVar rule: look up type in context and cross-check certificate
            (MicroCert::BVar { idx, ty }, MicroExpr::BVar(i)) => {
                if *idx != *i {
                    return Err(MicroError::InvalidBVar(*i));
                }
                let depth = self.context.len();
                if (*idx as usize) >= depth {
                    return Err(MicroError::InvalidBVar(*idx));
                }
                let ctx_pos = depth - 1 - *idx as usize;
                let ctx_ty = &self.context[ctx_pos];
                let lifted_ctx_ty = ctx_ty.lift(0, (depth - ctx_pos) as u32);
                if !self.def_eq_impl(ty.as_ref(), &lifted_ctx_ty)? {
                    return Err(MicroError::TypeMismatch {
                        expected: lifted_ctx_ty,
                        actual: ty.as_ref().clone(),
                    });
                }
                Ok(ty.as_ref().clone())
            }

            // Opaque rule: return declared type
            (MicroCert::Opaque { ty }, MicroExpr::Opaque(t)) => {
                if !self.def_eq_impl(ty.as_ref(), t.as_ref())? {
                    return Err(MicroError::TypeMismatch {
                        expected: ty.as_ref().clone(),
                        actual: t.as_ref().clone(),
                    });
                }
                Ok(ty.as_ref().clone())
            }

            // App rule: f a : B[a/x] when f : (x : A) → B and a : A
            (
                MicroCert::App {
                    fn_cert,
                    arg_cert,
                    result_ty,
                },
                MicroExpr::App(f, a),
            ) => {
                let fn_ty = self.verify_recurse(fn_cert, f)?;
                let fn_ty_whnf = self.whnf_impl(&fn_ty)?;

                let (expected_arg_ty, body_ty) = match &fn_ty_whnf {
                    MicroExpr::Pi(arg_ty, body) => (arg_ty.as_ref(), body.as_ref()),
                    _ => return Err(MicroError::ExpectedPi(fn_ty_whnf)),
                };

                let arg_ty = self.verify_recurse(arg_cert, a)?;

                if !self.def_eq_impl(&arg_ty, expected_arg_ty)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_arg_ty.clone(),
                        actual: arg_ty,
                    });
                }

                let expected_result = body_ty.instantiate(a);

                if !self.def_eq_impl(result_ty.as_ref(), &expected_result)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_result,
                        actual: result_ty.as_ref().clone(),
                    });
                }

                Ok(result_ty.as_ref().clone())
            }

            // Lam rule: λ (x : A). b : (x : A) → B
            (
                MicroCert::Lam {
                    arg_ty_cert,
                    body_cert,
                    result_ty,
                },
                MicroExpr::Lam(arg_ty, body),
            ) => {
                let arg_sort = self.verify_recurse(arg_ty_cert, arg_ty)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort)?;
                if !matches!(arg_sort_whnf, MicroExpr::Sort(_)) {
                    return Err(MicroError::ExpectedSort(arg_sort_whnf));
                }

                self.context.push(arg_ty.as_ref().clone());
                let body_ty = self.verify_recurse(body_cert, body);
                self.context.pop();
                let body_ty = body_ty?;

                let expected_pi = MicroExpr::Pi(arg_ty.clone(), Arc::new(body_ty));

                if !self.def_eq_impl(result_ty.as_ref(), &expected_pi)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_pi,
                        actual: result_ty.as_ref().clone(),
                    });
                }

                Ok(result_ty.as_ref().clone())
            }

            // Pi rule: (x : A) → B : Sort(imax(l1, l2))
            (
                MicroCert::Pi {
                    arg_ty_cert,
                    arg_level,
                    body_ty_cert,
                    body_level,
                },
                MicroExpr::Pi(arg_ty, body_ty),
            ) => {
                let arg_sort = self.verify_recurse(arg_ty_cert, arg_ty)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort)?;
                let l1 = match &arg_sort_whnf {
                    MicroExpr::Sort(level) => level.clone(),
                    other => return Err(MicroError::ExpectedSort(other.clone())),
                };

                if !self.universe_blind && !l1.level_eq(arg_level) {
                    return Err(MicroError::LevelMismatch {
                        expected: arg_level.clone(),
                        actual: l1,
                    });
                }

                self.context.push(arg_ty.as_ref().clone());
                let body_sort = self.verify_recurse(body_ty_cert, body_ty);
                self.context.pop();
                let body_sort = body_sort?;

                let body_sort_whnf = self.whnf_impl(&body_sort)?;
                let l2 = match &body_sort_whnf {
                    MicroExpr::Sort(level) => level.clone(),
                    other => return Err(MicroError::ExpectedSort(other.clone())),
                };

                if !self.universe_blind && !l2.level_eq(body_level) {
                    return Err(MicroError::LevelMismatch {
                        expected: body_level.clone(),
                        actual: l2,
                    });
                }

                Ok(MicroExpr::Sort(MicroLevel::imax(
                    arg_level.clone(),
                    body_level.clone(),
                )))
            }

            // Let rule: let x : A := v in b : B[v/x]
            (
                MicroCert::Let {
                    ty_cert,
                    val_cert,
                    body_cert,
                    result_ty,
                },
                MicroExpr::Let(ty, val, body),
            ) => {
                let ty_sort = self.verify_recurse(ty_cert, ty)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort)?;
                if !matches!(ty_sort_whnf, MicroExpr::Sort(_)) {
                    return Err(MicroError::ExpectedSort(ty_sort_whnf));
                }

                let val_ty = self.verify_recurse(val_cert, val)?;
                if !self.def_eq_impl(&val_ty, ty)? {
                    return Err(MicroError::TypeMismatch {
                        expected: ty.as_ref().clone(),
                        actual: val_ty,
                    });
                }

                self.context.push(ty.as_ref().clone());
                let body_ty = self.verify_recurse(body_cert, body);
                self.context.pop();
                let body_ty = body_ty?;

                let expected_result = body_ty.instantiate(val);

                if !self.def_eq_impl(result_ty.as_ref(), &expected_result)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_result,
                        actual: result_ty.as_ref().clone(),
                    });
                }

                Ok(result_ty.as_ref().clone())
            }

            // Lit rule: Lit(l) : ty (type provided by certificate)
            (MicroCert::Lit { lit, ty }, MicroExpr::Lit(l)) => {
                if lit != l {
                    return Err(MicroError::StructureMismatch);
                }
                Ok(ty.as_ref().clone())
            }

            // Proj rule: proj(idx, e) : field_ty (field type provided by certificate)
            (
                MicroCert::Proj {
                    idx,
                    expr_cert,
                    field_ty,
                },
                MicroExpr::Proj(i, e),
            ) => {
                if *idx != *i {
                    return Err(MicroError::StructureMismatch);
                }
                let _expr_ty = self.verify_recurse(expr_cert, e)?;
                Ok(field_ty.as_ref().clone())
            }

            // Structure mismatch
            _ => Err(MicroError::StructureMismatch),
        }
    }

    /// Consume one unit of reduction fuel. Returns `Err(Unsupported)` when
    /// exhausted, so a pathological term fails closed rather than looping.
    fn burn(&self) -> Result<(), MicroError> {
        let f = self.fuel.get();
        if f == 0 {
            return Err(MicroError::Unsupported(
                "micro-checker reduction fuel exhausted".to_string(),
            ));
        }
        self.fuel.set(f - 1);
        Ok(())
    }

    /// Weak head normal form: beta + zeta + DELTA (env const unfolding) +
    /// IOTA (native Nat/Bool reductions).
    ///
    /// Returns `Err(Unsupported)` only on fuel exhaustion; a stuck head (e.g.
    /// an unknown const applied to args) is returned AS-IS so the caller can
    /// detect non-reduction and fail closed at the def-eq comparison.
    #[cfg(test)]
    pub(crate) fn whnf(&self, e: &MicroExpr) -> MicroExpr {
        self.fuel.set(DEFAULT_FUEL);
        stack_safe(|| self.whnf_impl(e)).unwrap_or_else(|_| e.clone())
    }

    /// Implementation of WHNF (called via stacker::maybe_grow)
    fn whnf_impl(&self, e: &MicroExpr) -> Result<MicroExpr, MicroError> {
        stack_safe(|| self.whnf_core(e))
    }

    fn whnf_core(&self, e: &MicroExpr) -> Result<MicroExpr, MicroError> {
        self.burn()?;
        match e {
            // DELTA: unfold a reducible const to its body — EXCEPT the native
            // Nat ops, which we keep opaque to delta so only the native rule
            // reduces them (the prelude defines `Nat.add` etc. as `Nat.rec`
            // bodies we cannot model; see the spine branch).
            MicroExpr::Const(name) => {
                if is_native_op(name) {
                    return Ok(e.clone());
                }
                if let Some(entry) = self.env.get(name) {
                    if let Some(body) = &entry.body {
                        return self.whnf_impl(body);
                    }
                }
                Ok(e.clone())
            }
            MicroExpr::App(f, a) => {
                let f_whnf = self.whnf_impl(f)?;
                match &f_whnf {
                    // BETA
                    MicroExpr::Lam(_, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => {
                        // Collect the spine; try DELTA on the head const and
                        // native IOTA on Nat/Bool op heads.
                        let mut head = f_whnf;
                        let mut args: Vec<MicroExpr> = vec![a.as_ref().clone()];
                        // Flatten nested App in the head (f itself may be App).
                        while let MicroExpr::App(hf, ha) = &head {
                            args.push(ha.as_ref().clone());
                            head = self.whnf_impl(hf)?;
                        }
                        args.reverse();

                        if let MicroExpr::Const(name) = &head {
                            // IOTA-FIRST: native Nat/Bool reduction takes
                            // PRIORITY over delta. The prelude defines `Nat.add`
                            // etc. as `Nat.rec`-based definitions; unfolding
                            // those would replace a closed literal op with a
                            // recursor the micro-checker does not model. Trying
                            // the native rule first keeps the two reducers in
                            // agreement on closed arithmetic. (This is the
                            // micro-checker's OWN arithmetic — see `native`.)
                            if super::native::NAT_BINOPS.contains(&&**name) || &**name == "Nat.succ"
                            {
                                let mut red_args = Vec::with_capacity(args.len());
                                for arg in &args {
                                    red_args.push(self.whnf_impl(arg)?);
                                }
                                if let Some(r) = super::native::reduce_nat_app(name, &red_args) {
                                    return self.whnf_impl(&r);
                                }
                                // Native rule did not fire (e.g. a non-literal
                                // arg). Leave stuck rather than delta-unfolding
                                // into `Nat.rec` (which we cannot model) — the
                                // caller then fails closed.
                                let mut rebuilt = head.clone();
                                for arg in red_args {
                                    rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                                }
                                return Ok(rebuilt);
                            }
                            // IOTA on Bool ops (`Bool.beq` for now): reduce a
                            // pair of closed `Bool` constructors. Same priority
                            // rationale as the Nat ops.
                            if super::native::BOOL_BINOPS.contains(&&**name) {
                                let mut red_args = Vec::with_capacity(args.len());
                                for arg in &args {
                                    red_args.push(self.whnf_impl(arg)?);
                                }
                                if let Some(r) = super::native::reduce_bool_app(name, &red_args) {
                                    return self.whnf_impl(&r);
                                }
                                let mut rebuilt = head.clone();
                                for arg in red_args {
                                    rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                                }
                                return Ok(rebuilt);
                            }
                            // IOTA on a structural recursor (`Bool.rec` /
                            // `Nat.rec`): match the major premise's constructor
                            // and substitute the corresponding minor premise.
                            // This is the micro-checker's OWN recursor engine —
                            // it never calls the kernel reducer. Tried before
                            // DELTA so that e.g. `Bool.and`'s `Bool.rec` body
                            // (reached by unfolding) fires here.
                            if RECURSORS.contains(&&**name) {
                                if let Some(r) = self.reduce_recursor(name, &args)? {
                                    return self.whnf_impl(&r);
                                }
                                // Stuck recursor (major not a closed constructor,
                                // or wrong arity): leave the spine as-is so the
                                // caller fails closed (`Unsupported`), never a
                                // guessed result.
                                let mut rebuilt = head.clone();
                                for arg in args {
                                    rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                                }
                                return Ok(rebuilt);
                            }
                            // DELTA: unfold a reducible def head and re-apply.
                            if let Some(entry) = self.env.get(name) {
                                if let Some(body) = &entry.body {
                                    let mut applied = body.clone();
                                    for arg in &args {
                                        applied = MicroExpr::App(
                                            Arc::new(applied),
                                            Arc::new(arg.clone()),
                                        );
                                    }
                                    return self.whnf_impl(&applied);
                                }
                            }
                        }

                        // Stuck: rebuild the spine in normal form.
                        let mut rebuilt = head;
                        for arg in args {
                            rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                        }
                        Ok(rebuilt)
                    }
                }
            }
            // ZETA
            MicroExpr::Let(_, val, body) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            _ => Ok(e.clone()),
        }
    }

    /// IOTA for a structural recursor head (`Bool.rec` / `Nat.rec`), the
    /// micro-checker's OWN recursor engine.
    ///
    /// `args` is the recursor's argument spine in normal application order:
    /// `[motive, minor_0, .., minor_{k-1}, major, extra..]` (`k` = number of
    /// constructors). We whnf the MAJOR premise; if it is a closed constructor
    /// we substitute the corresponding minor premise (recursing on the
    /// predecessor for `Nat.succ`, exactly as iota does), re-applying any extra
    /// args. Returns:
    ///
    /// * `Ok(Some(reduced))` — the recursor fired (caller re-whnfs `reduced`),
    /// * `Ok(None)` — STUCK (major not a closed constructor, too few args, or an
    ///   unmodeled recursor shape) — the caller leaves the spine as-is so the
    ///   gate fails closed (`Unsupported`), never a guessed result.
    ///
    /// INDEPENDENCE: this is a hand-written re-implementation of constructor
    /// matching + minor-premise substitution. It NEVER calls the kernel's
    /// `whnf`/`is_def_eq`/recursor reduction — a kernel iota bug would surface
    /// here as a micro/kernel DISAGREEMENT.
    fn reduce_recursor(
        &self,
        name: &str,
        args: &[MicroExpr],
    ) -> Result<Option<MicroExpr>, MicroError> {
        self.burn()?;
        // Number of minor premises = number of constructors. `motive` precedes
        // them, the `major` premise follows; extra args (over-application) are
        // re-applied to the result.
        let num_minors = match name {
            "Bool.rec" | "Nat.rec" => 2,
            _ => return Ok(None),
        };
        // Layout: args[0] = motive, args[1..1+num_minors] = minors,
        // args[1+num_minors] = major, args[2+num_minors..] = extra.
        let major_idx = 1 + num_minors;
        if args.len() <= major_idx {
            // Recursor not yet fully applied to its major premise — stuck.
            return Ok(None);
        }
        let minors = &args[1..major_idx];
        let major = self.whnf_impl(&args[major_idx])?;
        let extra = &args[major_idx + 1..];

        let reduced = match name {
            "Bool.rec" => {
                let Some(b) = super::native::as_bool(&major) else {
                    return Ok(None);
                };
                // Constructor order: Bool.false = ctor 0, Bool.true = ctor 1.
                let minor = if b { &minors[1] } else { &minors[0] };
                minor.clone()
            }
            "Nat.rec" => {
                // Constructor order: Nat.zero = ctor 0 (no fields),
                // Nat.succ = ctor 1 (one field: the predecessor).
                match nat_constructor(&major) {
                    Some(NatCtor::Zero) => minors[0].clone(),
                    Some(NatCtor::Succ(pred)) => {
                        // minor_succ : (n : Nat) → motive n → motive (succ n).
                        // Apply to the predecessor and the recursive result:
                        //   minor_succ pred (Nat.rec motive minor0 minor1 pred)
                        let rec_on_pred = {
                            // Rebuild the recursor applied to `pred` only (no
                            // extra args — the extras belong to the final result
                            // of the OUTER recursor, applied below).
                            let mut spine = MicroExpr::Const(Arc::from(name));
                            spine = MicroExpr::App(Arc::new(spine), Arc::new(args[0].clone()));
                            for m in minors {
                                spine = MicroExpr::App(Arc::new(spine), Arc::new(m.clone()));
                            }
                            MicroExpr::App(Arc::new(spine), Arc::new(pred.clone()))
                        };
                        MicroExpr::App(
                            Arc::new(MicroExpr::App(Arc::new(minors[1].clone()), Arc::new(pred))),
                            Arc::new(rec_on_pred),
                        )
                    }
                    None => return Ok(None),
                }
            }
            _ => return Ok(None),
        };

        // Re-apply any over-application args to the reduced result.
        let mut out = reduced;
        for e in extra {
            out = MicroExpr::App(Arc::new(out), Arc::new(e.clone()));
        }
        Ok(Some(out))
    }

    /// Full normal form: whnf the head, then recurse into arguments of a
    /// stuck application and into a literal-equal comparison. Used by
    /// [`check_def_eq_result`] so e.g. `bvAdd 100 200` fully reduces to the
    /// `300` literal before structural comparison.
    fn whnf_full(&self, e: &MicroExpr) -> Result<MicroExpr, MicroError> {
        stack_safe(|| self.whnf_full_core(e))
    }

    fn whnf_full_core(&self, e: &MicroExpr) -> Result<MicroExpr, MicroError> {
        let w = self.whnf_impl(e)?;
        match &w {
            MicroExpr::App(f, a) => {
                let f2 = self.whnf_full(f)?;
                let a2 = self.whnf_full(a)?;
                // After normalizing args, a previously-stuck native op may now fire.
                let reassembled = MicroExpr::App(Arc::new(f2), Arc::new(a2));
                let w2 = self.whnf_impl(&reassembled)?;
                if self.structural_eq_impl(&w2, &reassembled) {
                    Ok(reassembled)
                } else {
                    self.whnf_full(&w2)
                }
            }
            other => Ok(other.clone()),
        }
    }

    /// Definitional equality check (structural after WHNF, env-aware).
    #[cfg(test)]
    pub(crate) fn def_eq(&self, a: &MicroExpr, b: &MicroExpr) -> bool {
        self.fuel.set(DEFAULT_FUEL);
        stack_safe(|| self.def_eq_impl(a, b)).unwrap_or(false)
    }

    /// Implementation of def_eq. Returns `Err(Unsupported)` on fuel
    /// exhaustion (propagated as fail-closed); otherwise `Ok(bool)`.
    fn def_eq_impl(&self, a: &MicroExpr, b: &MicroExpr) -> Result<bool, MicroError> {
        stack_safe(|| self.def_eq_core(a, b))
    }

    fn def_eq_core(&self, a: &MicroExpr, b: &MicroExpr) -> Result<bool, MicroError> {
        let a_whnf = self.whnf_impl(a)?;
        let b_whnf = self.whnf_impl(b)?;
        if self.structural_eq_impl(&a_whnf, &b_whnf) {
            return Ok(true);
        }
        // Congruence on applications, recursing through whnf (handles e.g.
        // `Eq Nat lhs lhs` vs `Eq Nat lhs' lhs'` where lhs ≡ lhs' by delta).
        if let (MicroExpr::App(f1, a1), MicroExpr::App(f2, a2)) = (&a_whnf, &b_whnf) {
            return Ok(self.def_eq_impl(f1, f2)? && self.def_eq_impl(a1, a2)?);
        }
        if let (MicroExpr::Pi(t1, b1), MicroExpr::Pi(t2, b2))
        | (MicroExpr::Lam(t1, b1), MicroExpr::Lam(t2, b2)) = (&a_whnf, &b_whnf)
        {
            return Ok(self.def_eq_impl(t1, t2)? && self.def_eq_impl(b1, b2)?);
        }
        Ok(false)
    }

    /// Structural equality (used after WHNF)
    #[cfg(test)]
    pub(crate) fn structural_eq(&self, a: &MicroExpr, b: &MicroExpr) -> bool {
        stack_safe(|| self.structural_eq_impl(a, b))
    }

    /// Implementation of structural_eq (called via stacker::maybe_grow)
    fn structural_eq_impl(&self, a: &MicroExpr, b: &MicroExpr) -> bool {
        stack_safe(|| self.structural_eq_core(a, b))
    }

    fn structural_eq_core(&self, a: &MicroExpr, b: &MicroExpr) -> bool {
        match (a, b) {
            (MicroExpr::BVar(i), MicroExpr::BVar(j)) => i == j,
            // Universe-blind in the env-aware path (see `universe_blind`).
            (MicroExpr::Sort(l1), MicroExpr::Sort(l2)) => self.universe_blind || l1.level_eq(l2),
            (MicroExpr::Const(n1), MicroExpr::Const(n2)) => n1 == n2,
            (MicroExpr::App(f1, a1), MicroExpr::App(f2, a2)) => {
                self.structural_eq_impl(f1, f2) && self.structural_eq_impl(a1, a2)
            }
            (MicroExpr::Lam(ty1, b1), MicroExpr::Lam(ty2, b2))
            | (MicroExpr::Pi(ty1, b1), MicroExpr::Pi(ty2, b2)) => {
                self.structural_eq_impl(ty1, ty2) && self.structural_eq_impl(b1, b2)
            }
            (MicroExpr::Let(ty1, v1, b1), MicroExpr::Let(ty2, v2, b2)) => {
                self.structural_eq_impl(ty1, ty2)
                    && self.structural_eq_impl(v1, v2)
                    && self.structural_eq_impl(b1, b2)
            }
            (MicroExpr::Opaque(t1), MicroExpr::Opaque(t2)) => self.structural_eq_impl(t1, t2),
            (MicroExpr::Lit(l1), MicroExpr::Lit(l2)) => l1 == l2,
            (MicroExpr::Proj(i1, e1), MicroExpr::Proj(i2, e2)) => {
                i1 == i2 && self.structural_eq_impl(e1, e2)
            }
            _ => false,
        }
    }
}

impl Default for MicroChecker<'static> {
    fn default() -> Self {
        Self::new()
    }
}
