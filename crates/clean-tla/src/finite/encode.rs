// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CIC encoding of a finite machine + the Bool reflection checker + the
//! kernel-closed proofs (blueprint S4).
//!
//! ## State representation — mixed-radix packing over `State := Nat`
//!
//! The blessed keystone (`TLAsem.InductiveInvariantSound`) is stated over
//! `State := Nat`. Rather than generalizing `State` across the whole T·SEM /
//! T·LIVE / T·REFINE tower, the multi-variable extension keeps the keystone
//! UNCHANGED and packs the record of cfg-bounded fields into one `Nat` with a
//! mixed-radix encoding: slot `i` (a scalar variable, or one Bool index of a
//! `Fin n → Bool` variable) has bound `Bᵢ` and weight `Wᵢ = Π_{j<i} Bⱼ`; a
//! state `(v₀…v_{k-1})` is `Σ vᵢ·Wᵢ`, and a field read is
//! `(s / Wᵢ) % Bᵢ` (`Nat.div`/`Nat.mod`, natively evaluated by the kernel on
//! literals). The packing is a bijection between the bounded record space and
//! `[0, Π Bᵢ)`; bounds are derived from the exhaustively-explored reachable
//! set, which is keyed on the certificate's cfg CONSTANT values.
//!
//! ## The three registered legs
//!
//! * `<thm>_check : Bool` — the reflection checker, a CLOSED Bool term that
//!   enumerates the J set (the reachable states) verifying init-membership,
//!   closure under every guarded action, and safety — as literal arithmetic
//!   the kernel can evaluate.
//! * `<thm>_check_eq_true : <thm>_check = true := Eq.refl true` — the `rfl`
//!   leg; accepting it forces the kernel to EVALUATE the checker.
//! * `<thm>_sound : <thm>_check = true → ∀ b, Runs Init Next b → Sat b (□
//!   Safety)` — the soundness lemma. Its proof instantiates the keystone with
//!   `J s := s = r₀ ∨ … ∨ s = r_{m-1}` (the reachable disjunction); the
//!   J⇒Safety leg consumes the `check = true` hypothesis (each per-state
//!   safety fact is EXTRACTED from it via the `Bool.and_eq_true_*` bridges),
//!   while initiation/consecution re-verify membership through kernel-checked
//!   `Or`-injections whose `Eq.refl` leaves the kernel re-evaluates.
//! * `<thm> : ∀ b, Runs Init Next b → Sat b (□ Safety) :=
//!   <thm>_sound <thm>_check_eq_true` — the final bare-conclusion product
//!   whose type α-matches [`crate::ty_cert::conclusion_ty`].
//!
//! Every leg is a real `Declaration` accepted by `Environment::add_decl` (the
//! kernel type-checker); no axiom, no `sorry`, and the `_assumed`-style
//! Pi-bound obligations never appear.

use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

use super::machine::{ActionSpec, EvalMode, Explored, FiniteMachine, Val, VarKind};
use super::parse::Tx;
use super::FiniteError;
use crate::semantics::B;

/// Cap on the packed-state space (product of slot bounds).
pub const MAX_PACKED_STATE: u128 = 1 << 32;

/// The fully-encoded product: four ready-to-register declarations plus the
/// evidence manifest.
#[derive(Debug, Clone)]
pub struct FiniteEncoded {
    /// Final theorem name (bare conclusion).
    pub thm_name: String,
    /// `<thm>_check` (Bool definition).
    pub check_name: String,
    /// `<thm>_check_eq_true` (the rfl leg).
    pub rfl_name: String,
    /// `<thm>_sound` (the soundness lemma).
    pub sound_name: String,
    /// Encoded `Init : Nat → Prop`.
    pub init: Expr,
    /// Encoded `Next : Nat → Nat → Prop`.
    pub next: Expr,
    /// Encoded `Safety : Nat → Prop` (all invariants conjoined, reflected).
    pub safety: Expr,
    /// Encoded `J : Nat → Prop` (reachable-state disjunction).
    pub j: Expr,
    /// The closed Bool checker term.
    pub check: Expr,
    /// Type of the soundness lemma.
    pub sound_type: Expr,
    /// Proof of the soundness lemma.
    pub sound_value: Expr,
    /// The independently-recomputable conclusion (α-comparison anchor).
    pub conclusion: Expr,
    /// Per-slot `(display, bound)` packing manifest.
    pub manifest: Vec<(String, u64)>,
    /// Packed values of the (given) reachable states, in order.
    pub reachable_packed: Vec<u64>,
    /// Number of Bool leaves conjoined in the checker.
    pub check_leaf_count: usize,
}

// ── small constructors ─────────────────────────────────────────────────────

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn lvl1() -> Level {
    Level::succ(Level::zero())
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn btrue() -> Expr {
    c("Bool.true")
}
fn bfalse() -> Expr {
    c("Bool.false")
}
fn band(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Bool.and"), [a, b])
}
fn bor(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Bool.or"), [a, b])
}
fn bnot(a: Expr) -> Expr {
    Expr::app(c("Bool.not"), a)
}
fn bimpl(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("TLAfin.bimpl"), [a, b])
}
fn cond_nat(cb: Expr, t: Expr, e: Expr) -> Expr {
    Expr::apps(c("TLAfin.cond"), [cb, t, e])
}
fn b2n(b: Expr) -> Expr {
    Expr::app(c("TLAfin.b2n"), b)
}
fn nadd(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [a, b])
}
fn nsub(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.sub"), [a, b])
}
fn nmul(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.mul"), [a, b])
}
fn ndiv(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.div"), [a, b])
}
fn nmod(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.mod"), [a, b])
}
fn beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.beq"), [a, b])
}
fn ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.ble"), [a, b])
}
fn eq_of(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![lvl1()]),
        [ty, a, b],
    )
}
fn eq_nat(a: Expr, b: Expr) -> Expr {
    eq_of(c("Nat"), a, b)
}
fn eq_bool_true(a: Expr) -> Expr {
    eq_of(c("Bool"), a, btrue())
}
fn eq_refl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]),
        [ty, a],
    )
}
fn eq_symm_nat(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![lvl1()]),
        [c("Nat"), a, b, h],
    )
}
fn eq_subst_nat(motive: Expr, a: Expr, b: Expr, h: Expr, pa: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![lvl1()]),
        [c("Nat"), motive, a, b, h, pa],
    )
}
fn and_p(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("And"), [a, b])
}
fn and_left(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("And.left"), [a, b, h])
}
fn and_right(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("And.right"), [a, b, h])
}
fn or_p(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Or"), [a, b])
}
fn or_inl(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("Or.inl"), [a, b, h])
}
fn or_inr(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("Or.inr"), [a, b, h])
}
fn or_rec(a: Expr, b: Expr, motive: Expr, fl: Expr, fr: Expr, disj: Expr) -> Expr {
    Expr::apps(c("Or.rec"), [a, b, motive, fl, fr, disj])
}
fn bool_no_confusion(goal: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
        [goal, bfalse(), btrue(), h],
    )
}
fn and_eq_true_left(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("Bool.and_eq_true_left"), [a, b, h])
}
fn and_eq_true_right(a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(c("Bool.and_eq_true_right"), [a, b, h])
}

// ── balanced Bool trees ────────────────────────────────────────────────────

/// Balanced `Bool.or` tree over disjunct leaves (evaluation-only positions).
fn bor_tree(xs: &[Expr]) -> Expr {
    match xs {
        [] => bfalse(),
        [x] => x.clone(),
        _ => {
            let mid = xs.len() / 2;
            bor(bor_tree(&xs[..mid]), bor_tree(&xs[mid..]))
        }
    }
}

/// A balanced `Bool.and` tree with retained subtree `Expr`s so extraction
/// paths reuse the EXACT (Arc-shared) subterms of the checker.
struct BandTree {
    /// The subtree's conjunction expression.
    expr: Expr,
    /// Leaf-index range `[lo, hi)` this subtree covers.
    lo: usize,
    hi: usize,
    /// Children (absent at leaves).
    children: Option<Box<(BandTree, BandTree)>>,
}

impl BandTree {
    fn build(leaves: &[Expr], lo: usize, hi: usize) -> BandTree {
        debug_assert!(lo < hi);
        if hi - lo == 1 {
            return BandTree {
                expr: leaves[lo].clone(),
                lo,
                hi,
                children: None,
            };
        }
        let mid = lo + (hi - lo) / 2;
        let l = Self::build(leaves, lo, mid);
        let r = Self::build(leaves, mid, hi);
        BandTree {
            expr: band(l.expr.clone(), r.expr.clone()),
            lo,
            hi,
            children: Some(Box::new((l, r))),
        }
    }

    /// `h : Eq Bool self.expr true` → `Eq Bool leaves[k] true` via the
    /// `Bool.and_eq_true_left/right` bridges.
    fn extract(&self, k: usize, h: Expr) -> Expr {
        debug_assert!(self.lo <= k && k < self.hi);
        match &self.children {
            None => h,
            Some(ch) => {
                let (l, r) = (&ch.0, &ch.1);
                if k < r.lo {
                    l.extract(k, and_eq_true_left(l.expr.clone(), r.expr.clone(), h))
                } else {
                    r.extract(k, and_eq_true_right(l.expr.clone(), r.expr.clone(), h))
                }
            }
        }
    }
}

// ── balanced Prop-Or trees ─────────────────────────────────────────────────

/// A balanced Prop-level `Or` tree over disjuncts, with retained subtree
/// `Expr`s so injections/eliminations reuse the exact (Arc-shared) subterms.
/// Balanced (not right-nested) for the same certified-inference-depth reason
/// as [`BandTree`].
struct OrTree {
    /// The subtree's disjunction proposition.
    expr: Expr,
    /// Leaf-index range `[lo, hi)` this subtree covers.
    lo: usize,
    hi: usize,
    /// Children (absent at leaves).
    children: Option<Box<(OrTree, OrTree)>>,
}

impl OrTree {
    fn build(ds: &[Expr], lo: usize, hi: usize) -> OrTree {
        debug_assert!(lo < hi);
        if hi - lo == 1 {
            return OrTree {
                expr: ds[lo].clone(),
                lo,
                hi,
                children: None,
            };
        }
        let mid = lo + (hi - lo) / 2;
        let l = Self::build(ds, lo, mid);
        let r = Self::build(ds, mid, hi);
        OrTree {
            expr: or_p(l.expr.clone(), r.expr.clone()),
            lo,
            hi,
            children: Some(Box::new((l, r))),
        }
    }

    fn build_all(ds: &[Expr]) -> OrTree {
        Self::build(ds, 0, ds.len())
    }

    /// Injection proof of disjunct `k` (given `leaf : dₖ`) into the tree.
    fn inject(&self, k: usize, leaf: Expr) -> Expr {
        debug_assert!(self.lo <= k && k < self.hi);
        match &self.children {
            None => leaf,
            Some(ch) => {
                let (l, r) = (&ch.0, &ch.1);
                if k < r.lo {
                    or_inl(l.expr.clone(), r.expr.clone(), l.inject(k, leaf))
                } else {
                    or_inr(l.expr.clone(), r.expr.clone(), r.inject(k, leaf))
                }
            }
        }
    }

    /// Case analysis: `leg(i) : dᵢ → goal` (lambda terms); result has type
    /// `goal`, consuming `scrut : self.expr`.
    fn elim(&self, scrut: Expr, goal: &Expr, leg: &dyn Fn(usize) -> Expr) -> Expr {
        match &self.children {
            None => Expr::app(leg(self.lo), scrut),
            Some(ch) => {
                let (l, r) = (&ch.0, &ch.1);
                let fl = {
                    let mut b = B::new();
                    let (h_id, h) = b.fresh();
                    let inner = l.elim(h, goal, leg);
                    b.lam(h_id, BinderInfo::Default, l.expr.clone(), inner)
                };
                let fr = {
                    let mut b = B::new();
                    let (h_id, h) = b.fresh();
                    let inner = r.elim(h, goal, leg);
                    b.lam(h_id, BinderInfo::Default, r.expr.clone(), inner)
                };
                let motive = {
                    let mut mb = B::new();
                    let (o_id, _o) = mb.fresh();
                    mb.lam(
                        o_id,
                        BinderInfo::Default,
                        or_p(l.expr.clone(), r.expr.clone()),
                        goal.clone(),
                    )
                };
                or_rec(l.expr.clone(), r.expr.clone(), motive, fl, fr, scrut)
            }
        }
    }
}

// ── the compiler ───────────────────────────────────────────────────────────

struct Cx<'a> {
    m: &'a FiniteMachine,
    weights: Vec<u64>,
    bounds: Vec<u64>,
}

impl<'a> Cx<'a> {
    /// `(s / Wᵢ) % Bᵢ` — the field read of slot `si` from packed state `s`.
    fn read_slot(&self, s: &Expr, si: usize) -> Expr {
        let divided = if self.weights[si] == 1 {
            s.clone()
        } else {
            ndiv(s.clone(), nat(self.weights[si]))
        };
        nmod(divided, nat(self.bounds[si]))
    }

    fn closed_index(&self, t: &Tx, binders: &mut Vec<(String, i64)>) -> Result<i64, FiniteError> {
        let mut state_reads = Vec::new();
        super::machine::collect_state_idents(t, self.m, &mut state_reads);
        if !state_reads.is_empty() {
            return Err(FiniteError::Fragment(format!(
                "function index reads state variables {state_reads:?} outside a binder \
                 (out of the Tier-0 fragment)"
            )));
        }
        let zero = vec![0i64; self.m.slots.len()];
        match self.m.eval(t, &zero, binders, EvalMode::IntExact)? {
            Val::I(n) => Ok(n),
            other => Err(FiniteError::Fragment(format!(
                "expected an integer index, got {other:?}"
            ))),
        }
    }

    /// Compile a Nat-valued term.
    fn int(&self, t: &Tx, s: &Expr, binders: &mut Vec<(String, i64)>) -> Result<Expr, FiniteError> {
        Ok(match t {
            Tx::Num(n) => {
                if *n < 0 {
                    return Err(FiniteError::NegativeValue {
                        context: format!("literal {n}"),
                    });
                }
                nat(*n as u64)
            }
            Tx::Ident(id) => {
                if let Some((_, v)) = binders.iter().rev().find(|(n, _)| n == id) {
                    if *v < 0 {
                        return Err(FiniteError::NegativeValue {
                            context: format!("binder {id} = {v}"),
                        });
                    }
                    return Ok(nat(*v as u64));
                }
                if let Some(cv) = self.m.consts.get(id) {
                    if *cv < 0 {
                        return Err(FiniteError::NegativeValue {
                            context: format!("CONSTANT {id} = {cv}"),
                        });
                    }
                    return Ok(nat(*cv as u64));
                }
                let vi = self
                    .m
                    .var_index(id)
                    .ok_or_else(|| FiniteError::Fragment(format!("unknown identifier {id}")))?;
                if self.m.vars[vi].kind != VarKind::Scalar {
                    return Err(FiniteError::Fragment(format!(
                        "function variable {id} used as an integer"
                    )));
                }
                let si = self
                    .m
                    .slot_index(vi, None)
                    .ok_or_else(|| FiniteError::Internal("missing scalar slot".into()))?;
                self.read_slot(s, si)
            }
            Tx::Add(a, b) => nadd(self.int(a, s, binders)?, self.int(b, s, binders)?),
            Tx::Sub(a, b) => nsub(self.int(a, s, binders)?, self.int(b, s, binders)?),
            Tx::Ite(cnd, x, y) => cond_nat(
                self.boolean(cnd, s, binders)?,
                self.int(x, s, binders)?,
                self.int(y, s, binders)?,
            ),
            other => {
                return Err(FiniteError::Fragment(format!(
                    "not a Nat-valued fragment term: {other:?}"
                )))
            }
        })
    }

    /// Compile a Bool-valued formula.
    fn boolean(
        &self,
        t: &Tx,
        s: &Expr,
        binders: &mut Vec<(String, i64)>,
    ) -> Result<Expr, FiniteError> {
        Ok(match t {
            Tx::BoolLit(true) => btrue(),
            Tx::BoolLit(false) => bfalse(),
            Tx::Eq(a, b) => beq(self.int(a, s, binders)?, self.int(b, s, binders)?),
            Tx::Neq(a, b) => bnot(beq(self.int(a, s, binders)?, self.int(b, s, binders)?)),
            Tx::Le(a, b) => ble(self.int(a, s, binders)?, self.int(b, s, binders)?),
            Tx::Lt(a, b) => ble(
                nadd(self.int(a, s, binders)?, nat(1)),
                self.int(b, s, binders)?,
            ),
            Tx::Ge(a, b) => ble(self.int(b, s, binders)?, self.int(a, s, binders)?),
            Tx::Gt(a, b) => ble(
                nadd(self.int(b, s, binders)?, nat(1)),
                self.int(a, s, binders)?,
            ),
            Tx::And(a, b) => band(self.boolean(a, s, binders)?, self.boolean(b, s, binders)?),
            Tx::Or(a, b) => bor(self.boolean(a, s, binders)?, self.boolean(b, s, binders)?),
            Tx::Not(a) => bnot(self.boolean(a, s, binders)?),
            Tx::Iff(a, b) => {
                let x = self.boolean(a, s, binders)?;
                let y = self.boolean(b, s, binders)?;
                bor(band(x.clone(), y.clone()), band(bnot(x), bnot(y)))
            }
            Tx::Ite(cnd, x, y) => {
                let cb = self.boolean(cnd, s, binders)?;
                let xt = self.boolean(x, s, binders)?;
                let yt = self.boolean(y, s, binders)?;
                bor(band(cb.clone(), xt), band(bnot(cb), yt))
            }
            Tx::FnAccess(f, idx) => {
                let vi = self
                    .m
                    .var_index(f)
                    .ok_or_else(|| FiniteError::Fragment(format!("unknown function var {f}")))?;
                let VarKind::FnBool { lo, hi } = self.m.vars[vi].kind else {
                    return Err(FiniteError::Fragment(format!(
                        "{f} is not a function variable"
                    )));
                };
                let k = self.closed_index(idx, binders)?;
                if k < lo || k > hi {
                    return Err(FiniteError::OutOfDomain {
                        fn_var: f.clone(),
                        index: k,
                    });
                }
                let si = self
                    .m
                    .slot_index(vi, Some(k))
                    .ok_or_else(|| FiniteError::Internal("missing fn slot".into()))?;
                beq(self.read_slot(s, si), nat(1))
            }
            Tx::Forall {
                binder,
                lo,
                hi,
                body,
            } => {
                let l = self.closed_index(lo, binders)?;
                let h = self.closed_index(hi, binders)?;
                let mut acc: Option<Expr> = None;
                for k in (l..=h).rev() {
                    binders.push((binder.clone(), k));
                    let inst = self.boolean(body, s, binders);
                    binders.pop();
                    let inst = inst?;
                    acc = Some(match acc {
                        None => inst,
                        Some(rest) => band(inst, rest),
                    });
                }
                acc.unwrap_or_else(btrue)
            }
            other => {
                return Err(FiniteError::Fragment(format!(
                    "not a Bool-valued fragment formula: {other:?}"
                )))
            }
        })
    }

    /// Compile the new value of one function-variable slot under an update.
    fn fn_bit(
        &self,
        upd: &Tx,
        var: usize,
        key: i64,
        s: &Expr,
        binders: &mut Vec<(String, i64)>,
    ) -> Result<Expr, FiniteError> {
        let vname = &self.m.vars[var].name;
        let VarKind::FnBool { lo, hi } = self.m.vars[var].kind else {
            return Err(FiniteError::Internal("fn_bit on scalar".into()));
        };
        let cur_slot = |cx: &Self| -> Result<Expr, FiniteError> {
            let si =
                cx.m.slot_index(var, Some(key))
                    .ok_or_else(|| FiniteError::Internal("missing fn slot".into()))?;
            Ok(cx.read_slot(s, si))
        };
        Ok(match upd {
            Tx::Ident(f) if f == vname => cur_slot(self)?,
            Tx::Comprehension {
                binder,
                lo: clo,
                hi: chi,
                body,
            } => {
                let l = self.closed_index(clo, binders)?;
                let h = self.closed_index(chi, binders)?;
                if l != lo || h != hi {
                    return Err(FiniteError::Fragment(format!(
                        "comprehension domain {l}..{h} does not match {vname}'s domain {lo}..{hi}"
                    )));
                }
                binders.push((binder.clone(), key));
                let r = self.boolean(body, s, binders);
                binders.pop();
                b2n(r?)
            }
            Tx::Except { base, index, value } => {
                if base != vname {
                    return Err(FiniteError::Fragment(format!(
                        "EXCEPT base {base} is not the updated variable {vname}"
                    )));
                }
                let idx = self.int(index, s, binders)?;
                let val = b2n(self.boolean(value, s, binders)?);
                cond_nat(beq(nat(key as u64), idx), val, cur_slot(self)?)
            }
            Tx::Ite(cnd, x, y) => cond_nat(
                self.boolean(cnd, s, binders)?,
                self.fn_bit(x, var, key, s, binders)?,
                self.fn_bit(y, var, key, s, binders)?,
            ),
            other => {
                return Err(FiniteError::Fragment(format!(
                    "unsupported function-update shape for {vname}: {other:?}"
                )))
            }
        })
    }

    /// The packed step function of `action` applied to state `s`.
    fn step(&self, action: &ActionSpec, s: &Expr) -> Result<Expr, FiniteError> {
        let mut acc: Option<Expr> = None;
        for (si, slot) in self.m.slots.iter().enumerate() {
            let upd = action.updates[slot.var].as_ref().ok_or_else(|| {
                FiniteError::Internal(format!("action {} missing an update", action.name))
            })?;
            let val = match (&self.m.vars[slot.var].kind, slot.key) {
                (VarKind::Scalar, None) => self.int(upd, s, &mut Vec::new())?,
                (VarKind::FnBool { .. }, Some(k)) => {
                    self.fn_bit(upd, slot.var, k, s, &mut Vec::new())?
                }
                _ => return Err(FiniteError::Internal("slot/var kind mismatch".into())),
            };
            let weighted = if self.weights[si] == 1 {
                val
            } else {
                nmul(val, nat(self.weights[si]))
            };
            acc = Some(match acc {
                None => weighted,
                Some(prev) => nadd(prev, weighted),
            });
        }
        acc.ok_or_else(|| FiniteError::Internal("machine with zero slots".into()))
    }

    /// The compiled guard of `action` at `s` (Bool; `true` when unguarded).
    fn guard(&self, action: &ActionSpec, s: &Expr) -> Result<Expr, FiniteError> {
        let mut acc: Option<Expr> = None;
        for g in action.guard.iter().rev() {
            let ge = self.boolean(g, s, &mut Vec::new())?;
            acc = Some(match acc {
                None => ge,
                Some(rest) => band(ge, rest),
            });
        }
        Ok(acc.unwrap_or_else(btrue))
    }

    /// The conjoined safety formula at `s` (Bool).
    fn safety(&self, s: &Expr) -> Result<Expr, FiniteError> {
        let mut acc: Option<Expr> = None;
        for (_, inv) in self.m.invariants.iter().rev() {
            let ie = self.boolean(inv, s, &mut Vec::new())?;
            acc = Some(match acc {
                None => ie,
                Some(rest) => band(ie, rest),
            });
        }
        acc.ok_or_else(|| FiniteError::Fragment("machine with zero invariants".into()))
    }
}

// ── the encoder ────────────────────────────────────────────────────────────

/// Encode the machine + explored reachable set into the four declarations.
///
/// `explored.reachable` is taken AS GIVEN (the mutation battery tampers it);
/// every fact derived from it is re-verified by the kernel, so a tampered set
/// yields a registration-time kernel rejection, never a wrong theorem.
pub fn encode_finite(
    m: &FiniteMachine,
    explored: &Explored,
    thm_name: &str,
) -> Result<FiniteEncoded, FiniteError> {
    let reach = &explored.reachable;
    if reach.is_empty() {
        return Err(FiniteError::Fragment("empty reachable set".into()));
    }
    let nslots = m.slots.len();
    for r in reach {
        if r.len() != nslots {
            return Err(FiniteError::Fragment(
                "reachable state has the wrong slot count".into(),
            ));
        }
        if r.iter().any(|v| *v < 0) {
            return Err(FiniteError::NegativeValue {
                context: "reachable state carries a negative slot".into(),
            });
        }
    }

    // Bounds from the reachable set (cfg-keyed via the exploration).
    let mut bounds = vec![1u64; nslots];
    for r in reach.iter().chain(std::iter::once(&m.init_slots)) {
        for (i, v) in r.iter().enumerate() {
            bounds[i] = bounds[i].max(*v as u64 + 1);
        }
    }
    let mut weights = vec![1u64; nslots];
    let mut prod: u128 = 1;
    for i in 0..nslots {
        weights[i] = prod as u64;
        prod = prod
            .checked_mul(bounds[i] as u128)
            .ok_or(FiniteError::PackOverflow)?;
        if prod > MAX_PACKED_STATE {
            return Err(FiniteError::PackOverflow);
        }
    }
    let pack = |st: &[i64]| -> u64 {
        st.iter()
            .enumerate()
            .map(|(i, v)| *v as u64 * weights[i])
            .sum()
    };

    let cx = Cx {
        m,
        weights: weights.clone(),
        bounds: bounds.clone(),
    };

    let packed: Vec<u64> = reach.iter().map(|r| pack(r)).collect();
    let positions: std::collections::BTreeMap<Vec<i64>, usize> = reach
        .iter()
        .enumerate()
        .map(|(i, r)| (r.clone(), i))
        .collect();
    let init_packed = pack(&m.init_slots);
    let init_pos = positions.get(&m.init_slots).copied().unwrap_or(0);

    // ── the four predicates ──
    let init_pred = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let body = eq_nat(s.clone(), nat(init_packed));
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), body))
    };
    let j_disjs_at =
        |x: &Expr| -> Vec<Expr> { packed.iter().map(|p| eq_nat(x.clone(), nat(*p))).collect() };
    let j_tree_at = |x: &Expr| -> OrTree { OrTree::build_all(&j_disjs_at(x)) };
    let j_pred = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let body = j_tree_at(&s).expr;
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), body))
    };
    let safety_pred = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let body = eq_bool_true(cx.safety(&s)?);
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), body))
    };
    let next_disjs_at = |s: &Expr, sp: &Expr| -> Result<Vec<Expr>, FiniteError> {
        m.actions
            .iter()
            .map(|a| {
                Ok(and_p(
                    eq_bool_true(cx.guard(a, s)?),
                    eq_nat(sp.clone(), cx.step(a, s)?),
                ))
            })
            .collect()
    };
    let next_pred = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let (sp_id, sp) = b.fresh();
        let body = OrTree::build_all(&next_disjs_at(&s, &sp)?).expr;
        let inner = b.lam(sp_id, BinderInfo::Default, c("Nat"), body);
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), inner))
    };
    let conclusion = crate::ty_cert::conclusion_ty(&init_pred, &next_pred, &safety_pred);

    // ── the checker leaves ──
    // Rust-side (NatTrunc = kernel semantics) evaluation of guards/successors.
    let mut guard_facts: Vec<Vec<(bool, Vec<i64>)>> = Vec::with_capacity(reach.len());
    for r in reach {
        let mut row = Vec::with_capacity(m.actions.len());
        for a in &m.actions {
            let g = eval_guard_nat(m, a, r)?;
            let succ = if g { fire_nat(m, a, r)? } else { Vec::new() };
            row.push((g, succ));
        }
        guard_facts.push(row);
    }

    let mem_b = |x: &Expr| -> Expr {
        let disjs: Vec<Expr> = packed.iter().map(|p| beq(x.clone(), nat(*p))).collect();
        bor_tree(&disjs)
    };

    let mut leaves: Vec<Expr> = Vec::new();
    leaves.push(mem_b(&nat(init_packed))); // init ⊆ J
    for p in &packed {
        leaves.push(cx.safety(&nat(*p))?); // J ⇒ Safety
    }
    for (ri, p) in packed.iter().enumerate() {
        let r_lit = nat(*p);
        for (ai, a) in m.actions.iter().enumerate() {
            // J closed under every guarded action. When the (Rust-side) guard
            // is enabled, the leaf verifies BOTH that the step function lands
            // exactly on the claimed successor literal (`beq(step r, r')` —
            // the kernel re-evaluates the packed step function) AND that the
            // successor is a member of J (`memB` over the literal). Keeping
            // the step evaluation OUT of the |J|-wide membership scan keeps
            // the kernel's evaluation (and its reduction certificates) linear
            // instead of quadratic. When the guard is disabled the leaf
            // asserts exactly that (`guard → false`); a wrong Rust-side guard
            // verdict makes the leaf evaluate false and the rfl leg refuse.
            let (guard_true, succ) = &guard_facts[ri][ai];
            let leaf = if *guard_true {
                let succ_lit = nat(pack(succ));
                bimpl(
                    cx.guard(a, &r_lit)?,
                    band(beq(cx.step(a, &r_lit)?, succ_lit.clone()), mem_b(&succ_lit)),
                )
            } else {
                bimpl(cx.guard(a, &r_lit)?, bfalse())
            };
            leaves.push(leaf);
        }
    }
    let check_leaf_count = leaves.len();
    // BALANCED conjunction tree: the kernel's certified inference/evaluation
    // walks the conjunction recursively, so a right-nested chain of n leaves
    // costs certificates quadratic in n; a balanced tree keeps the depth at
    // ⌈log₂ n⌉ (the Arc-shared subtrees also make the extraction lemma
    // arguments pointer-equal to the checker's own subterms).
    let check_tree = BandTree::build(&leaves, 0, leaves.len());
    let check = check_tree.expr.clone();

    let check_name = format!("{thm_name}_check");
    let rfl_name = format!("{thm_name}_check_eq_true");
    let sound_name = format!("{thm_name}_sound");
    // Extract `leaves[k] = true` from `h : check = true` by descending the
    // balanced tree with the `Bool.and_eq_true_left/right` prelude bridges.
    let extract = |hc: &Expr, k: usize| -> Expr { check_tree.extract(k, hc.clone()) };

    // ── hInit : ∀ s, Init s → J s ──
    let h_init = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let (h_id, h) = b.fresh();
        let init_lit = nat(init_packed);
        let j_at_init = j_tree_at(&init_lit).inject(init_pos, eq_refl(c("Nat"), init_lit.clone()));
        let hsym = eq_symm_nat(s.clone(), init_lit.clone(), h);
        let body = eq_subst_nat(j_pred.clone(), init_lit, s.clone(), hsym, j_at_init);
        let inner = b.lam(
            h_id,
            BinderInfo::Default,
            Expr::app(init_pred.clone(), s.clone()),
            body,
        );
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), inner))
    };

    // ── hCons : ∀ s s', J s → Next s s' → J s' ──
    let h_cons = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let (sp_id, sp) = b.fresh();
        let (hj_id, hj) = b.fresh();
        let (hn_id, hn) = b.fresh();
        let goal = Expr::app(j_pred.clone(), sp.clone());

        let mut legs: Vec<Expr> = Vec::with_capacity(reach.len());
        for (ri, p) in packed.iter().enumerate() {
            let r_lit = nat(*p);
            // perR : Next rᵢ s' → J s'
            let per_r = {
                let mut pb = B::new();
                let (hni_id, hni) = pb.fresh();
                let action_disjs = next_disjs_at(&r_lit, &sp)?;
                let mut action_legs: Vec<Expr> = Vec::with_capacity(m.actions.len());
                for (ai, a) in m.actions.iter().enumerate() {
                    let g_ty = eq_bool_true(cx.guard(a, &r_lit)?);
                    let s_ty = eq_nat(sp.clone(), cx.step(a, &r_lit)?);
                    let mut lb = B::new();
                    let (ha_id, ha) = lb.fresh();
                    let (guard_true, succ) = &guard_facts[ri][ai];
                    let body = if *guard_true {
                        let succ_pos = positions.get(succ).copied().unwrap_or(0);
                        let succ_packed = nat(pack(succ));
                        let hstep = and_right(g_ty.clone(), s_ty.clone(), ha);
                        let hsym = eq_symm_nat(sp.clone(), succ_packed.clone(), hstep);
                        let j_at_succ = j_tree_at(&succ_packed)
                            .inject(succ_pos, eq_refl(c("Nat"), succ_packed.clone()));
                        eq_subst_nat(j_pred.clone(), succ_packed, sp.clone(), hsym, j_at_succ)
                    } else {
                        // Guard is FALSE at rᵢ: the hypothesis `guard = true`
                        // evaluates to `false = true` — ex falso.
                        bool_no_confusion(goal.clone(), and_left(g_ty.clone(), s_ty.clone(), ha))
                    };
                    action_legs.push(lb.lam(ha_id, BinderInfo::Default, and_p(g_ty, s_ty), body));
                }
                let inner =
                    OrTree::build_all(&action_disjs).elim(hni, &goal, &|i| action_legs[i].clone());
                pb.lam(
                    hni_id,
                    BinderInfo::Default,
                    Expr::apps(next_pred.clone(), [r_lit.clone(), sp.clone()]),
                    inner,
                )
            };
            // motiveN := λ x, Next x s' → J s'
            let motive_n = {
                let mut mb = B::new();
                let (x_id, x) = mb.fresh();
                let body = Expr::arrow(
                    Expr::apps(next_pred.clone(), [x.clone(), sp.clone()]),
                    goal.clone(),
                );
                mb.lam(x_id, BinderInfo::Default, c("Nat"), body)
            };
            let mut lb = B::new();
            let (h_id, h) = lb.fresh();
            let transported = eq_subst_nat(
                motive_n,
                r_lit.clone(),
                s.clone(),
                eq_symm_nat(s.clone(), r_lit.clone(), h),
                per_r,
            );
            let body = Expr::app(transported, hn.clone());
            legs.push(lb.lam(
                h_id,
                BinderInfo::Default,
                eq_nat(s.clone(), r_lit.clone()),
                body,
            ));
        }
        let body = j_tree_at(&s).elim(hj, &goal, &|i| legs[i].clone());
        let l4 = b.lam(
            hn_id,
            BinderInfo::Default,
            Expr::apps(next_pred.clone(), [s.clone(), sp.clone()]),
            body,
        );
        let l3 = b.lam(
            hj_id,
            BinderInfo::Default,
            Expr::app(j_pred.clone(), s.clone()),
            l4,
        );
        let l2 = b.lam(sp_id, BinderInfo::Default, c("Nat"), l3);
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), l2))
    };

    // ── sound : check = true → conclusion ──
    let hc_ty = eq_bool_true(c(&check_name));
    let (sound_type, sound_value) = {
        let mut b = B::new();
        let (hc_id, hc) = b.fresh();
        // hSafe : ∀ s, J s → Safety s — extracts per-state safety facts from hc.
        let h_safe = {
            let mut sb = B::new();
            let (s_id, s) = sb.fresh();
            let (hj_id, hj) = sb.fresh();
            let goal = Expr::app(safety_pred.clone(), s.clone());
            let mut legs: Vec<Expr> = Vec::with_capacity(reach.len());
            for (ri, p) in packed.iter().enumerate() {
                let r_lit = nat(*p);
                let leaf = extract(&hc, 1 + ri);
                let mut lb = B::new();
                let (h_id, h) = lb.fresh();
                let body = eq_subst_nat(
                    safety_pred.clone(),
                    r_lit.clone(),
                    s.clone(),
                    eq_symm_nat(s.clone(), r_lit.clone(), h),
                    leaf,
                );
                legs.push(lb.lam(
                    h_id,
                    BinderInfo::Default,
                    eq_nat(s.clone(), r_lit.clone()),
                    body,
                ));
            }
            let body = j_tree_at(&s).elim(hj, &goal, &|i| legs[i].clone());
            let inner = sb.lam(
                hj_id,
                BinderInfo::Default,
                Expr::app(j_pred.clone(), s.clone()),
                body,
            );
            sb.lam(s_id, BinderInfo::Default, c("Nat"), inner)
        };
        let keystone = Expr::apps(
            c("TLAsem.InductiveInvariantSound"),
            [
                init_pred.clone(),
                next_pred.clone(),
                safety_pred.clone(),
                j_pred.clone(),
                h_init.clone(),
                h_cons.clone(),
                h_safe,
            ],
        );
        let value = b.finish(b.lam(hc_id, BinderInfo::Default, hc_ty.clone(), keystone));
        let ty = Expr::arrow(hc_ty.clone(), conclusion.clone());
        (ty, value)
    };

    let manifest = m
        .slots
        .iter()
        .zip(bounds.iter())
        .map(|(s, b)| (s.display.clone(), *b))
        .collect();

    Ok(FiniteEncoded {
        thm_name: thm_name.to_string(),
        check_name,
        rfl_name,
        sound_name,
        init: init_pred,
        next: next_pred,
        safety: safety_pred,
        j: j_pred,
        check,
        sound_type,
        sound_value,
        conclusion,
        manifest,
        reachable_packed: packed,
        check_leaf_count,
    })
}

/// Rust-side guard evaluation under the KERNEL's semantics (Nat truncation).
fn eval_guard_nat(m: &FiniteMachine, a: &ActionSpec, st: &[i64]) -> Result<bool, FiniteError> {
    for g in &a.guard {
        match m.eval(g, st, &mut Vec::new(), EvalMode::NatTrunc)? {
            Val::B(true) => {}
            Val::B(false) => return Ok(false),
            other => {
                return Err(FiniteError::Fragment(format!(
                    "guard of {} is not boolean: {other:?}",
                    a.name
                )))
            }
        }
    }
    Ok(true)
}

/// Rust-side successor computation under the KERNEL's semantics.
fn fire_nat(m: &FiniteMachine, a: &ActionSpec, st: &[i64]) -> Result<Vec<i64>, FiniteError> {
    let mut next = vec![0i64; m.slots.len()];
    for (vi, v) in m.vars.iter().enumerate() {
        let upd = a.updates[vi]
            .as_ref()
            .ok_or_else(|| FiniteError::Internal("missing update".into()))?;
        match (
            &v.kind,
            m.eval(upd, st, &mut Vec::new(), EvalMode::NatTrunc)?,
        ) {
            (VarKind::Scalar, Val::I(n)) => {
                let si = m
                    .slot_index(vi, None)
                    .ok_or_else(|| FiniteError::Internal("missing slot".into()))?;
                next[si] = n.max(0);
            }
            (VarKind::FnBool { lo, .. }, Val::F(bits)) => {
                for (off, bit) in bits.iter().enumerate() {
                    let si = m
                        .slot_index(vi, Some(lo + off as i64))
                        .ok_or_else(|| FiniteError::Internal("missing slot".into()))?;
                    next[si] = i64::from(*bit);
                }
            }
            (_, got) => {
                return Err(FiniteError::Fragment(format!(
                    "update of {} has the wrong shape: {got:?}",
                    v.name
                )))
            }
        }
    }
    Ok(next)
}
