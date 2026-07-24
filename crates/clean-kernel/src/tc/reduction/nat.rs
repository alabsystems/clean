// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat, Bool, and String literal reduction for the type checker.
//!
//! Handles closed arithmetic on Nat literals (add, sub, mul, div, mod, gcd,
//! pow, beq, ble, bitwise ops), Nat/String literal-to-constructor expansion,
//! and structural Nat equality via successor peeling.

use super::names;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use std::cell::Cell;

/// Structural nesting bound for the closed-Nat literal-extraction probe
/// (`get_nat_bignat_whnf`), beyond which `reduce_nat`'s UNARY
/// `Nat.succ`/`Nat.pred` collapse arms decline (see `nat_probe_depth` in
/// `tc/mod.rs`).
///
/// The bound is on PROBE NESTING DEPTH (a property of the mutual-recursion
/// shape), never on operand VALUES — value thresholds on this lane were
/// falsified twice (f27a290c). Legitimate nesting is tiny: a real proof
/// shape stacks at most a few probes (`Nat.succ (Nat.pred d)` — the
/// `Rat.effDenom` spelling — is 2; binop-operand nesting adds one per
/// syntactic level). `8` leaves those untouched with a wide margin; only a
/// per-VALUE-layer tower (one probe per materialized `Nat.succ`, e.g. a
/// 2^16-step `Nat.rec` walk under an omega certificate) can exceed it, and
/// exactly that tower is what the bound converts from Θ(major²)-work /
/// Θ(major)-stack recursion into the outer probes' existing Θ(major)
/// flat-iteration succ-peel.
const NAT_PROBE_MAX_DEPTH: u32 = 8;

impl<'env> TypeChecker<'env> {
    /// Check if an expression is Nat zero (either `Nat.zero` constructor or literal 0).
    ///
    /// Reference: Lean 4 type_checker.cpp:945-947 `is_nat_zero`
    pub(in crate::tc) fn is_nat_zero_expr(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Lit(Literal::Nat(n)) => matches!(n, BigNat::Small(0)),
            ExprKind::Const(name, levels) => levels.is_empty() && *name == *names::NAT_ZERO,
            _ => false,
        }
    }

    /// Check if an expression is a Nat successor and return the predecessor.
    ///
    /// Handles both:
    /// - Nat literal n > 0 -> returns Nat.lit(n-1)
    /// - Nat.succ(x) application -> returns x
    ///
    /// Reference: Lean 4 type_checker.cpp:949-961 `is_nat_succ`
    pub(in crate::tc) fn is_nat_succ_expr(e: &Expr) -> Option<Expr> {
        match &e.kind {
            ExprKind::Lit(Literal::Nat(n)) => {
                let pred = n.pred()?;
                Some(Expr::from_kind(ExprKind::Lit(Literal::Nat(pred))))
            }
            ExprKind::App(f, arg) => {
                if let ExprKind::Const(name, levels) = &f.kind {
                    if levels.is_empty() && *name == *names::NAT_SUCC {
                        return Some(arg.as_ref().clone());
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Structural Nat equality: peel successor layers.
    ///
    /// If both sides are Nat.zero (or literal 0), returns Some(true).
    /// If both sides are successors, recursively compares predecessors via is_def_eq_core.
    /// Otherwise returns None (cannot determine).
    ///
    /// Reference: Lean 4 type_checker.cpp:963-972 `is_def_eq_offset`
    pub(in crate::tc) fn is_def_eq_offset(&self, t: &Expr, s: &Expr) -> Option<bool> {
        if Self::is_nat_zero_expr(t) && Self::is_nat_zero_expr(s) {
            return Some(true);
        }
        // Fast path: two Nat LITERALS are def-eq iff equal — compare in O(1) on the
        // literal value. Without this, the successor-peel below (`is_nat_succ_expr`
        // decrements a literal by one per layer, recursing via `is_def_eq_impl`)
        // is Θ(min(a, b)): a FALSE equality between two ~10^18-scale literals — the
        // exact shape of two DISTINCT `Float` bit-patterns compared under `@Eq
        // Float (Float.mk a) (Float.mk b)` during a `rfl` check — peels ~10^18
        // successor layers and exhausts memory (25 GB+ before OOM-kill). A distinct
        // `Float`/`Nat` `rfl` must be a *loud, immediate* rejection, never a crash.
        if let (ExprKind::Lit(Literal::Nat(a)), ExprKind::Lit(Literal::Nat(b))) = (&t.kind, &s.kind)
        {
            return Some(a == b);
        }
        let mut pred_t = Self::is_nat_succ_expr(t);
        let mut pred_s = Self::is_nat_succ_expr(s);
        // Lean-parity single-step succ-peel across a grind-STUCK `Nat.add`.
        //
        // `native_nat_binop_grind_stuck` deliberately leaves `Nat.add a (closed
        // k >= 512)` unreduced to avoid the Θ(k) unary `Nat.rec` grind. That
        // stuck form also hides its leading successor from this offset check:
        // `Nat.add a k` IS `Nat.succ (Nat.add a (k-1))` (the add seed's ι-step on
        // `k = succ (k-1)`), but with the recursor never materialized, the head
        // stays `Nat.add`, not `Nat.succ`. When the OPPOSITE side is a *genuine*
        // `Nat.succ` / positive-literal successor, expose that one hidden
        // successor so the peel below fires — this is a real succ-vs-succ
        // reconciliation, never an add-vs-add cascade (the `Char.toUpper`
        // stuck-vs-stuck congruence, where NEITHER side is a genuine successor,
        // is untouched and still resolved structurally). Bounded: one layer per
        // call, consumed in lock-step with the opposite real-successor side.
        //
        // This recovers the `(x + 2048) + 1 =?= x + 2049`-shaped class (the Char
        // ordinal `ofOrdinal._proof_3` / `ordinal_ofOrdinal._proof_1_1` roots)
        // that Lean's kernel closes by full reduction, without reintroducing the
        // grind the guard exists to prevent.
        if pred_t.is_some() && pred_s.is_none() {
            pred_s = self.nat_add_succ_pred(s);
        } else if pred_s.is_some() && pred_t.is_none() {
            pred_t = self.nat_add_succ_pred(t);
        }
        if let (Some(pred_t), Some(pred_s)) = (pred_t, pred_s) {
            return Some(self.is_def_eq_impl(&pred_t, &pred_s));
        }
        None
    }

    /// View a `Nat.add a c` whose second operand `c` is a closed `Nat` literal
    /// `>= 1` as the successor `Nat.succ (Nat.add a (c-1))`, returning the
    /// predecessor `Nat.add a (c-1)`.
    ///
    /// Companion to [`native_nat_binop_grind_stuck`](Self::native_nat_binop_grind_stuck):
    /// that guard leaves such an add unreduced (to avoid the unary grind), which
    /// otherwise hides its leading `Nat.succ` from the structural succ-peel in
    /// [`is_def_eq_offset`](Self::is_def_eq_offset). This exposes exactly one
    /// successor layer.
    ///
    /// SOUNDNESS: `Nat.add a c` is *definitionally* `Nat.succ (Nat.add a (c-1))`
    /// for `c = succ (c-1)` (the `Nat.add` seed's ι-step), and `Nat.succ` is an
    /// injective constructor, so `is_def_eq_offset` peeling one layer preserves
    /// def-eq exactly in both directions — it never accepts a pair Lean rejects,
    /// nor rejects one Lean accepts. Only the bare `Nat.add` head with a
    /// literal-reducible second operand is recognized; a symbolic count (`c`
    /// whnf's to no literal) or `c = 0` returns `None`, so it strictly extends
    /// the offset relation to the grind-stuck adds and nothing else.
    ///
    /// SCOPE (perf-critical): only a *symbolic* (fvar-bearing) add is viewed as
    /// a successor. A CLOSED `Nat.add 7 <big k> =?= <lit>` must stay with the
    /// `reduce_nat` hook one line below the offset check in the lazy-delta loop
    /// (`def_eq/delta.rs`), which computes it in O(1); peeling it here would
    /// recurse Θ(k) — for a `2^32`-scale count that exhausts the heartbeat and
    /// would wrongly fail-close a pair Lean accepts instantly. The fvar
    /// condition confines the peel to exactly the grind-stuck domain (a closed
    /// add is never left stuck on the lazy-delta path: `reduce_nat` reduces it
    /// right after this check declines).
    fn nat_add_succ_pred(&self, e: &Expr) -> Option<Expr> {
        if !e.has_fvar_quick() {
            return None;
        }
        if e.get_app_num_args() != 2 {
            return None;
        }
        let ExprKind::App(f_a, c) = &e.kind else {
            return None;
        };
        let ExprKind::App(head, _a) = &f_a.kind else {
            return None;
        };
        let ExprKind::Const(name, levels) = &head.kind else {
            return None;
        };
        if !levels.is_empty() || *name != *names::NAT_ADD {
            return None;
        }
        // `c` must reduce to a closed literal >= 1 (its predecessor exists).
        let pred_c = self.get_nat_bignat_whnf(c)?.pred()?;
        // Reuse the `Nat.add a` prefix (`f_a`) with the decremented count.
        Some(Expr::app(
            f_a.as_ref().clone(),
            Expr::from_kind(ExprKind::Lit(Literal::Nat(pred_c))),
        ))
    }

    /// Reduce closed Nat arithmetic to a literal.
    ///
    /// Handles Nat.succ, Nat.add, Nat.sub, Nat.mul, Nat.div, Nat.mod, Nat.gcd,
    /// Nat.pow, Nat.beq, Nat.ble, and bitwise operations.
    ///
    /// Reference: Lean 4 type_checker.cpp:611-640 `reduce_nat`
    pub(in crate::tc) fn reduce_nat(&self, e: &Expr) -> Option<Expr> {
        let nargs = e.get_app_num_args();

        if nargs == 1 {
            // Probe non-re-entrancy (see `nat_probe_depth` in `tc/mod.rs` and
            // `NAT_PROBE_MAX_DEPTH` above): past the structural probe-nesting
            // bound, decline the unary collapse arms. Without this, each
            // `Nat.rec` iota step materializes one `Nat.succ` layer whose
            // whnf-core `reduce_nat` hook fires this arm, whose probe re-whnfs
            // the ENTIRE remaining tower — one native stack frame and a full
            // re-derivation per layer (Θ(major²) work; the ToInt omega-frame
            // hang). Declining here is verdict-neutral: `Nat.succ X` is
            // already a legitimate constructor-headed WHNF (symbolic towers
            // return it today); every literal consumer goes through the
            // probes' iterative succ-peel, which extracts the identical
            // BigNat in Θ(major) flat iteration; and `succ (…) =?= lit` pairs
            // close via `is_def_eq_offset`. Production whnf calls run at
            // depth 0 and are untouched.
            if self.nat_probe_depth.get() > NAT_PROBE_MAX_DEPTH {
                return None;
            }
            // Unary: Nat.succ — arbitrary precision (succ of any closed Nat, e.g.
            // succ(2^128) = 2^128 + 1), via the multi-limb BigNat add path.
            if let ExprKind::App(f, arg) = &e.kind {
                if let ExprKind::Const(name, levels) = &f.kind {
                    if levels.is_empty() && *name == *names::NAT_SUCC {
                        if let Some(v) = self.get_nat_bignat_whnf(arg) {
                            return Some(Expr::bignat_lit(v.checked_add_big(&BigNat::Small(1))));
                        }
                    }
                    // Unary: Nat.pred — arbitrary precision, O(1) on the literal.
                    //
                    // `Nat.pred 0 = 0`, `Nat.pred (n+1) = n` (Lean floored
                    // semantics: pred is truncated at zero). `BigNat::pred()`
                    // returns `None` for zero, which we map to `0`.
                    //
                    // WHY THIS MATTERS: `Rat.Raw.effDenom x` is SYNTACTICALLY
                    // `Nat.succ (Nat.pred (Rat.denom x))`, and `Rat.le` lifts its
                    // comparisons through `effDenom`. Without this arm, `Nat.pred`
                    // delta-unfolds to its `Nat.rec`-based definition, which
                    // materializes a `succ∘pred` chain of depth O(value) — OOM/
                    // SIGKILL past a ~2^16 denominator. With it, `Nat.pred (2^1074)`
                    // (and any large-denominator `Rat.le`) reduces in bounded,
                    // O(1)-on-the-literal time. Parity with `Nat.succ` above; the
                    // pre-check in whnf fires this BEFORE the def is ever unfolded.
                    if levels.is_empty() && *name == *names::NAT_PRED {
                        if let Some(v) = self.get_nat_bignat_whnf(arg) {
                            return Some(Expr::bignat_lit(v.pred().unwrap_or(BigNat::Small(0))));
                        }
                    }
                }
            }
        } else if nargs == 2 {
            // Binary: extract `f a1 a2` where f = app_fn(app_fn(e))
            if let ExprKind::App(f_a1, a2) = &e.kind {
                if let ExprKind::App(f, a1) = &f_a1.kind {
                    if let ExprKind::Const(name, levels) = &f.kind {
                        if !levels.is_empty() {
                            return None;
                        }
                        // Arbitrary-precision Nat reduction via the multi-limb BigNat
                        // path (parity with Lean 4's mpz kernel). Closes kernel parity
                        // gap #9: operands and results no longer capped at u128.
                        if *name == *names::NAT_ADD {
                            return self
                                .reduce_bin_bignat_op(a1, a2, |x, y| Some(x.checked_add_big(y)));
                        }
                        if *name == *names::NAT_SUB {
                            // Lean Nat subtraction is truncated (floored) at zero.
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| {
                                Some(x.saturating_sub_big(y))
                            });
                        }
                        if *name == *names::NAT_MUL {
                            // checked_mul_big returns None past the 16-limb bound.
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| x.checked_mul_big(y));
                        }
                        if *name == *names::NAT_DIV {
                            // Lean semantics: n / 0 = 0 (checked_div_big handles this).
                            return self
                                .reduce_bin_bignat_op(a1, a2, |x, y| Some(x.checked_div_big(y)));
                        }
                        if *name == *names::NAT_MOD {
                            // Lean semantics: n % 0 = n (checked_mod_big handles this).
                            return self
                                .reduce_bin_bignat_op(a1, a2, |x, y| Some(x.checked_mod_big(y)));
                        }
                        if *name == *names::NAT_GCD {
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| Some(x.gcd_big(y)));
                        }
                        if *name == *names::NAT_POW {
                            return self.reduce_nat_pow(a1, a2);
                        }
                        if *name == *names::NAT_BEQ {
                            return self.reduce_bin_bignat_pred(a1, a2, |x, y| x == y);
                        }
                        if *name == *names::NAT_BLE {
                            return self.reduce_bin_bignat_pred(a1, a2, |x, y| x <= y);
                        }
                        if *name == *names::NAT_LAND {
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| Some(x.bitand_big(y)));
                        }
                        if *name == *names::NAT_LOR {
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| Some(x.bitor_big(y)));
                        }
                        if *name == *names::NAT_XOR {
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| Some(x.bitxor_big(y)));
                        }
                        if *name == *names::NAT_SHIFT_LEFT {
                            // Bound the shift to keep allocation bounded (parity with the
                            // env native reducer: > 1024 bits / 16 limbs stays unreduced).
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| {
                                if x.is_zero() {
                                    return Some(BigNat::Small(0));
                                }
                                let shift = y.to_u64()?;
                                if shift > 1024 {
                                    return None;
                                }
                                let result = x.checked_shl_big(shift as usize);
                                if result.limbs().len() > 16 {
                                    None
                                } else {
                                    Some(result)
                                }
                            });
                        }
                        if *name == *names::NAT_SHIFT_RIGHT {
                            return self.reduce_bin_bignat_op(a1, a2, |x, y| {
                                let shift = y.to_u64()?;
                                if shift > u64::MAX / 2 {
                                    // Shift exceeds any representable bit position.
                                    return Some(BigNat::Small(0));
                                }
                                Some(x.shr_big(shift as usize))
                            });
                        }
                    }
                }
            }
        }
        None
    }

    /// Whnf-reduce `e` then extract its closed BigNat value (owned).
    ///
    /// Handles the `Nat.zero` constructor and any `Nat` literal (Small or Big).
    /// Returns `None` for expressions that are not closed Nats.
    ///
    /// ITERATIVE SUCC PEELING (#20 deep-recheck): a closed Nat can be a
    /// `Nat.succ (Nat.succ (… base))` chain of depth O(value). The previous
    /// implementation reduced such a chain by recursion — `whnf_impl(Nat.succ X)`
    /// fires `reduce_nat`'s unary-succ branch, which calls
    /// `get_nat_bignat_whnf(X)` -> `whnf_impl(X)` -> … — building O(depth) native
    /// stack frames that escape the WHNF trampoline (this is the residual
    /// recursion that overflowed the 256 MiB re-check on the deep carry/borrow
    /// ALU ops: slt/sle/ult/ule/eq/neg/add/sub). The deep refutations' `litNeg`
    /// /`Nat.rec` peels produce exactly these long succ chains.
    ///
    /// Here we peel `Nat.succ` layers in a LOOP, accumulating the successor
    /// count, then add it to the fully-reduced base. This is bit-identical to the
    /// recursive collapse: `Nat.succ` is a constructor, so `value(succ^k base) =
    /// k + value(base)`. ZERO soundness effect — pure evaluation strategy.
    /// `pub(in crate::tc)` re-export of `get_nat_bignat_whnf` for the sibling
    /// `Int` reducer (`reduction::int`), which must extract a `Nat` operand
    /// (e.g. an effDenom argument `Nat.succ (Nat.pred …)`) to a literal before
    /// applying the arbitrary-precision `Int` operation.
    pub(in crate::tc) fn get_nat_bignat_whnf_pub(&self, e: &Expr) -> Option<BigNat> {
        self.get_nat_bignat_whnf(e)
    }

    /// The four guarded native Nat binops: `Nat.add`/`Nat.sub`/`Nat.mul`/
    /// `Nat.pow` — the ops whose seeds recurse structurally on the 2nd
    /// operand and whose delta-unfolding therefore materializes a Θ(count)
    /// unary recursor walk. Shared name set between
    /// [`native_nat_binop_grind_stuck`](Self::native_nat_binop_grind_stuck)
    /// (the mixed-operand large-count stuck guard at the WHNF App pre-check
    /// and `get_delta_const`) and the bare-Const eager-unfold deferral in
    /// `try_unfold_definition` (whnf_proj.rs), which keeps the op folded
    /// until its arguments re-attach so the App-arm `reduce_nat` can
    /// accelerate the closed case in binary.
    pub(in crate::tc) fn is_guarded_nat_binop_name(name: &Name) -> bool {
        *name == *names::NAT_ADD
            || *name == *names::NAT_SUB
            || *name == *names::NAT_MUL
            || *name == *names::NAT_POW
    }

    /// SOUNDNESS / Lean-parity: a native Nat op whose `reduce_nat` fast path has
    /// just DECLINED (an operand is non-literal) but whose STRUCTURAL RECURSION
    /// COUNT — the 2nd operand, which the `Nat.add`/`Nat.sub`/`Nat.mul`/`Nat.pow`
    /// seeds recurse on — is a LARGE closed `Nat` literal would, if delta-unfolded,
    /// iota-iterate `Nat.rec` `count` times over the *symbolic* first operand: a
    /// unary grind of size Θ(count). This is exactly the carrier-tower perf class
    /// — e.g. an omega/`decide` certificate forces `Nat.sub m 2^31`, which
    /// delta-unfolds to `Nat.rec m (λ _ ih => Nat.pred ih) 2^31` and grinds ~2^31
    /// `Nat.pred` steps, exhausting the deterministic heartbeat.
    ///
    /// Lean's kernel never performs this reduction on these proofs: its `is_def_eq`
    /// stays structural / lazy-delta and never forces the huge unary unfolding
    /// (a synthetic `rfl` that forces it hits Lean's `maxRecDepth` and bails). We
    /// match that by leaving the op **stuck** here. This is:
    ///
    /// - **Sound** (never a wrong ACCEPT): the stuck `Nat.sub m n` IS definitionally
    ///   equal to its unfolded form, so declining to unfold can only make a
    ///   comparison *fail to converge* (a stuck-vs-stuck structural match still
    ///   succeeds); it can never equate two non-def-eq terms. It strictly *narrows*
    ///   the reduction relation, never widens def-eq.
    /// - **Completeness-preserving for every real proof**: no proof `rfl`-reduces
    ///   `Nat.sub m k` for a large *closed* `k` (that unary normal form is not
    ///   feasibly checkable in Lean either). SMALL closed counts (`< THRESHOLD`)
    ///   and SYMBOLIC counts (`Nat.succ m`, as needed by `Nat.succ_sub_succ` and
    ///   friends) are UNAFFECTED — `get_nat_bignat_whnf` returns `None` for a
    ///   symbolic-rooted count, so the guard declines and the op unfolds as before.
    ///
    /// Only the 2nd-argument-recursing ops are covered; `Nat.div`/`Nat.mod`/`Nat.gcd`
    /// have distinct fuel / well-founded seeds that already stay stuck on symbolic
    /// inputs.
    pub(in crate::tc) fn native_nat_binop_grind_stuck(&self, name: &Name, e: &Expr) -> bool {
        /// Recursion-count magnitude at or above which a mixed (symbolic-operand)
        /// native Nat op is left stuck rather than unfolded into a unary grind.
        /// Chosen at `2^9 = 512` — comfortably ABOVE any count a legitimate
        /// definitional proof reduces by hand (single/low double digits, and the
        /// `2^7`/`2^8 = 128/256` `Int8`/`UInt8`-carrier constants, which reduce
        /// cheaply and correctly in-budget), yet AT-OR-BELOW every perf-class
        /// grind: `Char.numSurrogates = 2048`, `2^15 = 32768` (`Int16`),
        /// `2^31`/`2^32` (`Int32`/`ISize`/`UInt32`), and `Char.numCodePoints =
        /// 1112064`. Because the stuck form is def-eq to the unfolded form and
        /// these grinds are *correct but slow*, leaving them stuck is a pure,
        /// sound perf win: the omega/`decide` certificates then verify by
        /// structural congruence (as Lean's kernel does), instead of a Θ(count)
        /// unary `Nat.rec` walk that (accumulated over a proof) blows the
        /// deterministic heartbeat.
        const NATIVE_NAT_GRIND_STUCK_THRESHOLD: u64 = 1 << 9;

        if !Self::is_guarded_nat_binop_name(name) {
            return false;
        }
        if e.get_app_num_args() != 2 {
            return false;
        }
        // e = App(App(Const, a1), a2); the seeds recurse on the 2nd operand a2.
        let ExprKind::App(f_a1, a2) = &e.kind else {
            return false;
        };
        if !matches!(&f_a1.kind, ExprKind::App(..)) {
            return false;
        }
        let count = self.get_nat_bignat_whnf(a2);
        let fired = match &count {
            Some(BigNat::Small(v)) => *v >= NATIVE_NAT_GRIND_STUCK_THRESHOLD,
            Some(BigNat::Big(_)) => true,
            None => false,
        };
        #[cfg(feature = "reduction-stats")]
        crate::tc::reduction_stats::record_binop_guard(name, a2, count.as_ref(), fired);
        fired
    }

    /// SOUNDNESS / Lean-parity companion to `native_nat_binop_grind_stuck`: the
    /// SAME large-closed-recursion-count grind, but recognized at the recursor
    /// AFTER a native `Nat.add`/`Nat.sub`/… definition has already been
    /// delta-unfolded to its `Nat.rec` seed.
    ///
    /// The head-keyed `native_nat_binop_grind_stuck` fires only when WHNF sees a
    /// 2-argument `Nat.add`-HEADED application at the App pre-check. But a
    /// `Nat.add` reached as an application *head* — e.g. through the
    /// `HAdd.hAdd`/instance-projection spine `(instHAdd Nat instAddNat).hAdd a b`
    /// — is whnf'd to its lambda by `beta_or_iota_step`'s head reduction and
    /// beta-reduced DIRECTLY into `Nat.rec (fun _ => Nat) a (fun _ ih => Nat.succ
    /// ih) b`, never presenting a guardable `Nat.add`-headed app. That bypass is
    /// the residual carrier grind (live-traced 2026-07-07 on
    /// `Char.toUpper._proof_1`: `Nat.add (UInt32.toNat (Char.val c))
    /// (UInt32.toNat ('A'.val - 'a'.val))`, count `2^32 - 32 = 4294967264`, a
    /// ~4.3-billion-step unary walk that never terminates).
    ///
    /// This recognizes the *materialized* grind recursor and lets the caller
    /// leave it stuck. Fires iff `e` is `Nat.rec (fun _ => Nat) z s major` with:
    /// - motive `fun _ => Nat` — a NAT-valued recursor (`Nat.add`/`Nat.sub`/
    ///   `Nat.pow` seed); this EXCLUDES the `Bool`-motive `Nat.decLt`/`Nat.ble`
    ///   towers (whose base is `Bool.false`), which are a separate, genuinely
    ///   finite decision reduction we must not block;
    /// - `major` (the recursion count) whnfs to a closed literal `>= 2^9` — the
    ///   same threshold and rationale as `native_nat_binop_grind_stuck`;
    /// - `z` (the zero-case accumulator = the binop's symbolic first operand) is
    ///   fvar-bearing. A CLOSED `z` is a fully-closed computation that yields a
    ///   genuine literal (Lean computes it via GMP) — we must not block it.
    ///
    /// SOUNDNESS: identical to `native_nat_binop_grind_stuck`. The stuck
    /// `Nat.rec … major` IS definitionally equal to its ι-normal form, so
    /// declining to expand it strictly NARROWS reduction — a comparison can only
    /// fail to converge (never a wrong ACCEPT). It matches Lean, whose
    /// `@[extern]` `Nat.add`/`Nat.sub` stay stuck on a symbolic operand and never
    /// materialize this unary tower. The `z`-symbolic + large-closed-`major`
    /// condition is exactly the pair the head guard already leaves stuck on the
    /// raw-`Nat.add` path; this closes the projection-spine bypass with the same
    /// verdict-neutral effect.
    pub(in crate::tc) fn native_nat_grind_recursor_stuck(&self, e: &Expr) -> bool {
        const NATIVE_NAT_GRIND_STUCK_THRESHOLD: u64 = 1 << 9;

        let head = e.get_app_fn();
        let ExprKind::Const(name, _) = &head.kind else {
            return false;
        };
        if *name != *names::NAT_REC {
            return false;
        }
        // Nat has no params/indices: `Nat.rec {motive} z s major` = 4 app args.
        if e.get_app_num_args() != 4 {
            return false;
        }
        let args = e.get_app_args();
        let (motive, z, major) = (args[0], args[1], args[3]);

        // Motive must be `fun _ => Nat` — a NAT-valued recursor. Excludes the
        // `Bool`-motive `Nat.decLt`/`Nat.ble` decision towers (closed base).
        let ExprKind::Lam(_, _, body) = &motive.kind else {
            return false;
        };
        let ExprKind::Const(motive_ret, _) = &body.kind else {
            return false;
        };
        if *motive_ret != *names::NAT {
            return false;
        }

        // The accumulator must be symbolic (the binop's symbolic first operand).
        // A closed `z` is a genuine finite computation; do not block it.
        if !z.has_fvar_quick() {
            return false;
        }

        // The recursion count must be a large closed literal.
        match self.get_nat_bignat_whnf(major) {
            Some(BigNat::Small(v)) => v >= NATIVE_NAT_GRIND_STUCK_THRESHOLD,
            Some(BigNat::Big(_)) => true,
            None => false,
        }
    }

    fn get_nat_bignat_whnf(&self, e: &Expr) -> Option<BigNat> {
        // Track probe nesting for the dynamic extent of this extraction (the
        // `whnf_impl` below can re-enter `reduce_nat`, whose arms re-enter
        // this probe on nested operands). See `nat_probe_depth` (tc/mod.rs)
        // and `NAT_PROBE_MAX_DEPTH`: past the bound, the unary succ/pred
        // collapse arms decline and THIS loop's iterative succ-peel does the
        // consuming instead. RAII so early `return`s in the loop unwind it.
        struct ProbeDepthGuard<'a>(&'a Cell<u32>);
        impl Drop for ProbeDepthGuard<'_> {
            fn drop(&mut self) {
                self.0.set(self.0.get().saturating_sub(1));
            }
        }
        self.nat_probe_depth
            .set(self.nat_probe_depth.get().saturating_add(1));
        let _probe_guard = ProbeDepthGuard(&self.nat_probe_depth);

        let mut succs = BigNat::Small(0);
        let mut cur = e.clone();
        loop {
            // Peel any SYNTACTIC `Nat.succ`/literal-successor layers WITHOUT
            // re-entering whnf (so a raw `Nat.succ (Nat.succ …)` chain is
            // consumed iteratively, never recursively). `is_nat_succ_expr`
            // returns the predecessor for both `Nat.succ x` apps and `Nat.lit
            // n>0`; for a literal it peels exactly one and yields `Nat.lit n-1`,
            // which the literal arm below handles in O(1) — so we only spin on
            // genuine `Nat.succ` constructor spines.
            if let ExprKind::App(f, arg) = &cur.kind {
                if let ExprKind::Const(name, levels) = &f.kind {
                    if levels.is_empty() && *name == *names::NAT_SUCC {
                        succs = succs.checked_add_big(&BigNat::Small(1));
                        let next = arg.as_ref().clone();
                        cur = next;
                        continue;
                    }
                }
            }
            // Head is not a syntactic succ-app: reduce it to WHNF once. Because
            // `reduce_nat`'s unary-succ branch now delegates to THIS function
            // (which is iterative), the recursion through `whnf_impl` no longer
            // grows the stack per succ layer.
            let cur_whnf = self.whnf_impl(&cur);
            match &cur_whnf.kind {
                ExprKind::Lit(Literal::Nat(n)) => {
                    return Some(succs.checked_add_big(n));
                }
                ExprKind::Const(name, levels) if levels.is_empty() && *name == *names::NAT_ZERO => {
                    return Some(succs);
                }
                // WHNF may expose a fresh `Nat.succ` head (e.g. after delta /
                // iota): loop to peel it iteratively rather than recursing.
                ExprKind::App(f, _) => {
                    if let ExprKind::Const(name, levels) = &f.kind {
                        if levels.is_empty() && *name == *names::NAT_SUCC {
                            cur = cur_whnf;
                            continue;
                        }
                    }
                    return None;
                }
                _ => return None,
            }
        }
    }

    /// Reduce a binary Nat arithmetic operation over arbitrary-precision BigNats.
    ///
    /// Both operands are whnf-reduced and extracted as full BigNats (no u128 cap),
    /// giving parity with Lean 4's mpz kernel. The `op` may return `None` to leave
    /// the expression unreduced (e.g. a bounded multiply/shift exceeding the limb cap).
    fn reduce_bin_bignat_op(
        &self,
        a1: &Expr,
        a2: &Expr,
        op: impl FnOnce(&BigNat, &BigNat) -> Option<BigNat>,
    ) -> Option<Expr> {
        let v1 = self.get_nat_bignat_whnf(a1)?;
        let v2 = self.get_nat_bignat_whnf(a2)?;
        op(&v1, &v2).map(Expr::bignat_lit)
    }

    /// Reduce Nat.pow over arbitrary-precision BigNats.
    ///
    /// Both base and exponent are extracted as full BigNats. `checked_pow_big`
    /// bounds the result at 1024 bits (16 limbs) and the exponent at 1023, so a
    /// BigNat base raised past that bound stays unreduced rather than blowing up —
    /// a documented allocation guard, replacing the old u128/2^24-exp cap.
    /// Lean 4 uses mpz (unbounded) here; the bound is the only divergence and is
    /// the same one the env-level native `Nat.pow` reducer already uses.
    ///
    /// Reference: Lean 4 type_checker.cpp:588-599
    fn reduce_nat_pow(&self, a1: &Expr, a2: &Expr) -> Option<Expr> {
        let base = self.get_nat_bignat_whnf(a1)?;
        let exp = self.get_nat_bignat_whnf(a2)?;
        base.checked_pow_big(&exp).map(Expr::bignat_lit)
    }

    /// Reduce a binary Nat predicate (returns Bool.true or Bool.false).
    ///
    /// Operands are compared as full BigNats (no u128 cap).
    /// Reference: Lean 4 type_checker.cpp:601-609 `reduce_bin_nat_pred`
    fn reduce_bin_bignat_pred(
        &self,
        a1: &Expr,
        a2: &Expr,
        pred: impl FnOnce(&BigNat, &BigNat) -> bool,
    ) -> Option<Expr> {
        let v1 = self.get_nat_bignat_whnf(a1)?;
        let v2 = self.get_nat_bignat_whnf(a2)?;
        if pred(&v1, &v2) {
            Some(Expr::const_(names::BOOL_TRUE.clone(), vec![]))
        } else {
            Some(Expr::const_(names::BOOL_FALSE.clone(), vec![]))
        }
    }
}

/// Convert a Nat literal to constructor form.
///
/// For n = 0, returns `Nat.zero`.
/// For n > 0, returns `Nat.succ (Nat.lit (n-1))` - lazy expansion.
/// Per Lean 4's `nat_lit_to_constructor` in `kernel/inductive.cpp` (lines 1191-1198).
///
/// Lazy expansion avoids O(n) memory for large literals and prevents stack overflow.
/// Subsequent iota reductions will recursively expand as needed.
pub(super) fn nat_lit_to_constructor(n: &BigNat) -> Expr {
    match n.pred() {
        None => Expr::const_(names::NAT_ZERO.clone(), vec![]),
        Some(pred) => {
            // Lazy expansion: Nat.succ (Nat.lit (n-1))
            Expr::app(
                Expr::const_(names::NAT_SUCC.clone(), vec![]),
                Expr::from_kind(ExprKind::Lit(Literal::Nat(pred))),
            )
        }
    }
}

/// Convert a String literal to constructor form.
///
/// Transforms a string into `String.ofList (List.cons c1 (List.cons c2 ... List.nil))`.
/// Per Lean 4's `string_lit_to_constructor` in `kernel/inductive.cpp`.
pub(crate) fn string_lit_to_constructor(s: &str) -> Expr {
    // Lean 4 uses String.ofList, not String.mk (see kernel/inductive.cpp line 1226)
    let string_of_list = Expr::const_(names::STRING_OF_LIST.clone(), vec![]);
    // List.nil : {a : Type u} -> List a
    // For Char (which is Type 0), use universe level 0
    let list_nil = Expr::const_(names::LIST_NIL.clone(), vec![Level::zero()]);
    let list_cons = names::LIST_CONS.clone();
    let char_type = Expr::const_(names::CHAR.clone(), vec![]);

    // Build the list of characters from right to left
    // List.nil {Char}
    let mut char_list = Expr::app(list_nil.clone(), char_type.clone());

    // Process characters in reverse order to build the list
    for c in s.chars().rev() {
        // Char.ofNat : Nat -> Char
        let char_val = Expr::app(
            Expr::const_(names::CHAR_OF_NAT.clone(), vec![]),
            Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(c as u64)))),
        );

        // List.cons : {a : Type u} -> a -> List a -> List a
        // For Char (Type 0), use universe level 0
        char_list = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(list_cons.clone(), vec![Level::zero()]),
                    char_type.clone(),
                ),
                char_val,
            ),
            char_list,
        );
    }

    // String.ofList char_list
    Expr::app(string_of_list, char_list)
}
