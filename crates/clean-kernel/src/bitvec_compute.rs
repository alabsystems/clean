// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computational fixed-width BitVec layer — the *semantically real* successor to
//! [`crate::bitvec_slice`].
//!
//! # What this is
//!
//! Where [`crate::bitvec_slice`] declares `BV`/`getBit`/`bvAdd`/`bvSub` as
//! **opaque uninterpreted symbols** (sound only for the identical-operand /
//! reflexive slice), this module gives the bitvector ops **honest computational
//! definitions** and proves **non-reflexive** bitvector identities as genuine
//! kernel theorems whose transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`.
//!
//! ## Representation (width 4, honestly reported)
//!
//! A width-4 bitvector is a single-constructor inductive (a structure)
//!
//! ```text
//!   inductive Clean.BV4 where
//!     | mk (b0 b1 b2 b3 : Bool) : Clean.BV4      -- b0 = LSB
//! ```
//!
//! with reducible bit accessors `Clean.BV4.bitK : Clean.BV4 → Bool`
//! (`K ∈ {0,1,2,3}`) defined by `Clean.BV4.rec` (exactly as core `Bool.not`
//! is defined by `Bool.rec`). All operations are **real reducible
//! `Definition`s**, not axioms:
//!
//!   * `bvZero : Clean.BV4 := mk false false false false`
//!   * `bvNot v := mk (not b0) (not b1) (not b2) (not b3)`
//!   * `bvAdd x y` — ripple-carry: per-bit `sum = xor3(xᵢ,yᵢ,cᵢ)`,
//!     `carryₒᵤₜ = maj(xᵢ,yᵢ,cᵢ)`, carry-in `false`.
//!   * `bvSub x y := bvAddCarry x (bvNot y) true` — two's-complement
//!     subtraction (`a - b = a + ¬b + 1`), carry-in `true`.
//!   * `bvEq x y : Prop` — the `And`-chain of per-bit accessor equalities
//!     (definitionally, same shape as the slice layer's `bvEq`).
//!
//! `xor3` / `maj` are themselves reducible defs over `Bool.xor` / `Bool.and` /
//! `Bool.or`.
//!
//! ## What is PROVED (kernel theorems, axiom closure ⊆ foundational)
//!
//!   * `Clean.BV4.bvSub_self : (a : Clean.BV4) → bvEq (bvSub a a) bvZero`
//!     — the NON-REFLEXIVE self-difference identity `a - a = 0`. The LHS
//!     `bvSub a a` and the RHS `bvZero` are genuinely DIFFERENT terms; the proof
//!     is real per-bit / carry-chain Boolean reasoning over a SYMBOLIC `a`
//!     (4-way nested `Bool.rec` case analysis on `a`'s bits, leaves by
//!     reflexivity after the kernel ι/δ-reduces the adder), NOT computation on a
//!     literal and NOT reflexivity-in-disguise.
//!   * `Clean.BV4.bvAdd_zero : (a : Clean.BV4) → bvEq (bvAdd a bvZero) a`
//!     — additive identity `a + 0 = a`.
//!   * `Clean.BV4.bvAdd_comm : (a b : Clean.BV4) → bvEq (bvAdd a b) (bvAdd b a)`
//!     — commutativity (stretch goal; full 4+4-bit case split).
//!   * the per-bit full-adder sum/carry leaf relations are *discharged by the
//!     kernel's own ι-reduction* inside these proofs (they are not asserted).
//!
//! ## Width generalization (the gate-fidelity layer is now width-N)
//!
//! The *gate-fidelity* layer — the computational carrier, the bit accessors, the
//! ripple-carry `bvAdd`/`bvSub`, and the per-bit `bvEq` — is **parametric in an
//! arbitrary width `N`** via [`Environment::init_bv_compute_width`] and the
//! [`BvNames`] name-builder. For width `N` it registers `Clean.BV{N}` with an
//! `N`-argument `mk`, `N` reducible bit accessors `bit0..bit{N-1}`, an `N`-bit
//! ripple-carry `bvAdd`/`bvSub`, and an `N`-conjunct `bvEq`. The width-N adder is
//! a FAITHFUL ripple-carry: output bit `i` is `xor3(xᵢ, yᵢ, cᵢ)` with carry
//! `cᵢ₊₁ = maj(xᵢ, yᵢ, cᵢ)` — so the kernel re-check of a width-N bit-blast
//! reduces the *actual* width-N gate trees (a wrong-bit / wrong-width encoding is
//! REJECTED by `check_type`). The `xor3`/`maj`/`xnor` primitives and the Bool
//! helper theorems are width-INDEPENDENT (`Bool → Bool`) and shared across widths.
//!
//! [`Environment::init_bv_compute`] (no width arg) remains the concrete **4-bit**
//! instantiation `Clean.BV4` and, additionally, registers the fully-PROVED
//! non-reflexive identities `bvSub_self` / `bvAdd_zero` / `bvAdd_comm` (axiom
//! closure ⊆ FOUNDATIONAL). Those proofs use a full `Bool.rec` case split over
//! ALL operand bits (256 leaves at width 4), which is EXPONENTIAL in `N` and is
//! deliberately NOT generalized — they are not on the criterion-2 lowering path
//! (the bridge recovers the identity from the bit-blast `Unsat`, never citing
//! `bvAdd_comm`). See the report at the end of `init_bv_compute_width`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::{
    BinderInfo, Constructor, Declaration, EnvError, Environment, Expr, InductiveDecl,
    InductiveType, Level,
};

/// The computational layer bit width. Concrete 4-bit (see module honesty note).
pub const BV_COMPUTE_WIDTH: u32 = 4;

/// Names of the declarations the computational layer registers.
pub mod names {
    /// The width-4 bitvector carrier (single-constructor inductive / structure).
    pub const BV: &str = "Clean.BV4";
    /// The constructor `mk (b0 b1 b2 b3 : Bool) : Clean.BV4`.
    pub const BV_MK: &str = "Clean.BV4.mk";
    /// Reducible per-bit accessors `Clean.BV4 → Bool`.
    pub const BIT: [&str; 4] = [
        "Clean.BV4.bit0",
        "Clean.BV4.bit1",
        "Clean.BV4.bit2",
        "Clean.BV4.bit3",
    ];
    /// `xor3 : Bool → Bool → Bool → Bool` (full-adder sum bit).
    pub const XOR3: &str = "Clean.BV4.xor3";
    /// `maj : Bool → Bool → Bool → Bool` (full-adder carry bit).
    pub const MAJ: &str = "Clean.BV4.maj";
    /// `bvZero : Clean.BV4`.
    pub const BV_ZERO: &str = "Clean.BV4.bvZero";
    /// `bvNot : Clean.BV4 → Clean.BV4`.
    pub const BV_NOT: &str = "Clean.BV4.bvNot";
    /// `bvAdd : Clean.BV4 → Clean.BV4 → Clean.BV4` (carry-in false).
    pub const BV_ADD: &str = "Clean.BV4.bvAdd";
    /// `bvSub : Clean.BV4 → Clean.BV4 → Clean.BV4` (a + ¬b + 1).
    pub const BV_SUB: &str = "Clean.BV4.bvSub";
    /// Defined per-bit equality `Clean.BV4 → Clean.BV4 → Prop`.
    pub const BV_EQ: &str = "Clean.BV4.bvEq";
    /// `bvSub_self : (a) → bvEq (bvSub a a) bvZero`.
    pub const BV_SUB_SELF: &str = "Clean.BV4.bvSub_self";
    /// `bvAdd_zero : (a) → bvEq (bvAdd a bvZero) a`.
    pub const BV_ADD_ZERO: &str = "Clean.BV4.bvAdd_zero";
    /// `bvAdd_comm : (a b) → bvEq (bvAdd a b) (bvAdd b a)`.
    pub const BV_ADD_COMM: &str = "Clean.BV4.bvAdd_comm";
    /// IR-side full-adder SUM gate `xor3Ir a b c := Bool.xor a (Bool.xor b c)` —
    /// RIGHT-associated, a syntactically DIFFERENT term from `xor3` (left-assoc).
    pub const XOR3_IR: &str = "Clean.BV4.xor3Ir";
    /// IR-side full-adder CARRY (majority) gate
    /// `majIr a b c := Bool.or (Bool.and a b) (Bool.and c (Bool.or a b))` — a
    /// DIFFERENT boolean expression for the majority than `maj` (OR-of-pairwise-ANDs).
    pub const MAJ_IR: &str = "Clean.BV4.majIr";
    /// IR-side ripple adder `bvAddIr : BV4 → BV4 → BV4` (separately defined via
    /// `xor3Ir`/`majIr`; the machine-vs-IR fidelity theorem proves it equals `bvAdd`).
    pub const BV_ADD_IR: &str = "Clean.BV4.bvAddIr";
    /// `bvAdd_eq_ir : (x y) → bvEq (bvAdd x y) (bvAddIr x y)` — the machine-side
    /// (`bvAdd`, the decoded-emitted-bytes adder shape) equals the IR-side
    /// (`bvAddIr`, the IR-spec adder shape), PROVEN (not rfl: distinct terms).
    pub const BV_ADD_EQ_IR: &str = "Clean.BV4.bvAdd_eq_ir";
    /// `xnor : Bool → Bool → Bool` — `not (xor a b)` (full bit-equality gate).
    pub const XNOR: &str = "Clean.BV4.xnor";
    /// `boolEm : (b : Bool) → Or (Eq b true) (Eq b false)` — Bool totality.
    pub const BOOL_EM: &str = "Clean.BV4.boolEm";
    /// `eqTfElim : (b : Bool) → Eq b true → Eq b false → False` — contradiction.
    pub const EQ_TF_ELIM: &str = "Clean.BV4.eqTfElim";
    /// `xnorTrueImpEq : (x y : Bool) → Eq (xnor x y) true → Eq x y`.
    pub const XNOR_TRUE_IMP_EQ: &str = "Clean.BV4.xnorTrueImpEq";
    /// `litClash : (b : Bool) → Eq b true → Eq (Bool.not b) true → False`.
    ///
    /// The resolution-pivot contradiction: a literal and its negation (`b` and
    /// `Bool.not b`) cannot both `Holds`. Used to discharge every pivot of the
    /// solver-derived kernel resolution refutation.
    pub const LIT_CLASH: &str = "Clean.BV4.litClash";
    /// `notFalseImpTrue : (b : Bool) → Eq b false → Eq (Bool.not b) true`.
    ///
    /// `Holds`-of-negation introduction: a `false` bit makes its negation literal
    /// `Holds`. Used to discharge the disequality clause (`¬e_i`) when some per-bit
    /// equality var is `false`.
    pub const NOT_FALSE_IMP_TRUE: &str = "Clean.BV4.notFalseImpTrue";
    /// `eqImpXnorTrue : (x y : Bool) → Eq x y → Eq (xnor x y) true`.
    ///
    /// The XnorEq gate's positive direction: equal bits make the bit-equality var
    /// `Holds`. Lets the solver-backed reconstruction discharge each per-bit unit
    /// `Holds(e_i)` from the per-bit equality the proved `bvAdd_comm` certifies.
    pub const EQ_IMP_XNOR_TRUE: &str = "Clean.BV4.eqImpXnorTrue";
}

/// Width-parametric name builder for the computational BitVec layer.
///
/// For a width `N` the carrier is `Clean.BV{N}` with constructor `Clean.BV{N}.mk`,
/// bit accessors `Clean.BV{N}.bit{k}` (`k ∈ 0..N`), and ops `bvZero`/`bvNot`/
/// `bvAdd`/`bvSub`/`bvEq` under the same namespace. The Bool-level gate primitives
/// (`xor3`/`maj`/`xnor`) and the Bool helper theorems (`boolEm`/`eqTfElim`/
/// `xnorTrueImpEq`/`litClash`/`notFalseImpTrue`/`eqImpXnorTrue`) are
/// width-INDEPENDENT and live under the SHARED `Clean.BV4.*` namespace (so a single
/// copy is reused across all widths — they are `Bool → Bool` and carry no width).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BvNames {
    /// The bit width `N`.
    pub width: u32,
}

impl BvNames {
    /// A name builder for width `N`.
    #[must_use]
    pub const fn new(width: u32) -> Self {
        Self { width }
    }
    /// The carrier name `Clean.BV{N}`.
    #[must_use]
    pub fn bv(self) -> String {
        format!("Clean.BV{}", self.width)
    }
    /// The constructor `Clean.BV{N}.mk`.
    #[must_use]
    pub fn bv_mk(self) -> String {
        format!("Clean.BV{}.mk", self.width)
    }
    /// The `k`-th bit accessor `Clean.BV{N}.bit{k}`.
    #[must_use]
    pub fn bit(self, k: u32) -> String {
        format!("Clean.BV{}.bit{}", self.width, k)
    }
    /// `Clean.BV{N}.bvZero`.
    #[must_use]
    pub fn bv_zero(self) -> String {
        format!("Clean.BV{}.bvZero", self.width)
    }
    /// `Clean.BV{N}.bvNot`.
    #[must_use]
    pub fn bv_not(self) -> String {
        format!("Clean.BV{}.bvNot", self.width)
    }
    /// `Clean.BV{N}.bvAdd`.
    #[must_use]
    pub fn bv_add(self) -> String {
        format!("Clean.BV{}.bvAdd", self.width)
    }
    /// `Clean.BV{N}.bvSub`.
    #[must_use]
    pub fn bv_sub(self) -> String {
        format!("Clean.BV{}.bvSub", self.width)
    }
    /// `Clean.BV{N}.bvXor` (bitwise XOR; per-bit `Bool.xor`, no carry).
    #[must_use]
    pub fn bv_xor(self) -> String {
        format!("Clean.BV{}.bvXor", self.width)
    }
    /// `Clean.BV{N}.bvAnd` (bitwise AND; per-bit `Bool.and`, no carry).
    #[must_use]
    pub fn bv_and(self) -> String {
        format!("Clean.BV{}.bvAnd", self.width)
    }
    /// `Clean.BV{N}.bvOr` (bitwise OR; per-bit `Bool.or`, no carry).
    #[must_use]
    pub fn bv_or(self) -> String {
        format!("Clean.BV{}.bvOr", self.width)
    }
    /// `Clean.BV{N}.bvEq`.
    #[must_use]
    pub fn bv_eq(self) -> String {
        format!("Clean.BV{}.bvEq", self.width)
    }
}

// ── small Expr helpers ────────────────────────────────────────────────────────

fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn bnot(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Bool.not"), x)
}
fn bxor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.xor"), [x, y])
}
fn band(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.and"), [x, y])
}
fn bor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.or"), [x, y])
}

fn bv_ty_w(nm: BvNames) -> Expr {
    Expr::const_str(&nm.bv())
}
fn bv_ty() -> Expr {
    bv_ty_w(BvNames::new(BV_COMPUTE_WIDTH))
}

/// `Clean.BV{N}.mk b0 .. b{N-1}`.
fn bv_mk_w(nm: BvNames, bits: &[Expr]) -> Expr {
    debug_assert_eq!(bits.len() as u32, nm.width, "mk arity must equal width");
    Expr::apps(Expr::const_str(&nm.bv_mk()), bits.iter().cloned())
}
/// `Clean.BV4.mk b0 b1 b2 b3` (the width-4 convenience used by the proved theorems).
fn bv_mk(bits: [Expr; 4]) -> Expr {
    bv_mk_w(BvNames::new(4), &bits)
}

/// `Clean.BV{N}.bit{k} v`.
fn bit_w(nm: BvNames, v: Expr, k: u32) -> Expr {
    Expr::app(Expr::const_str(&nm.bit(k)), v)
}
/// `Clean.BV4.bitK v` (width-4 accessor; public for back-compat).
pub fn bit(v: Expr, k: u32) -> Expr {
    bit_w(BvNames::new(4), v, k)
}

/// `xor3 a b c`.
fn xor3(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::XOR3), [a, b, c])
}
/// `maj a b c`.
fn maj(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::MAJ), [a, b, c])
}
/// `xor3Ir a b c` (IR-side, right-associated sum).
fn xor3_ir(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::XOR3_IR), [a, b, c])
}
/// `majIr a b c` (IR-side, `(a&&b) || (c && (a||b))` majority).
fn maj_ir(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::MAJ_IR), [a, b, c])
}

/// `Clean.BV{N}.bvEq x y : Prop`.
fn bv_eq_w(nm: BvNames, x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str(&nm.bv_eq()), [x, y])
}
/// `Clean.BV4.bvEq x y : Prop` (width-4; public for back-compat).
pub fn bv_eq(x: Expr, y: Expr) -> Expr {
    bv_eq_w(BvNames::new(4), x, y)
}

/// `Clean.BV{N}.bvEq x y : Prop` for the layer width carried by `nm`.
pub fn bv_eq_for(nm: BvNames, x: Expr, y: Expr) -> Expr {
    bv_eq_w(nm, x, y)
}

/// `Clean.BV{N}.bit{k} v` for the layer width carried by `nm`.
pub fn bit_for(nm: BvNames, v: Expr, k: u32) -> Expr {
    bit_w(nm, v, k)
}

/// `@Eq.{1} Bool x y`.
fn eq_bool(x: Expr, y: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [bool_ty(), x, y],
    )
}

impl Environment {
    /// Register the computational width-4 BitVec layer and its proved identities.
    ///
    /// Idempotent. Requires `Bool`, `Eq`, `And`, `True`; initializes them if
    /// absent. All registered ops are reducible `Definition`s; the identities are
    /// kernel-checked `Theorem`s with axiom closure `⊆ FOUNDATIONAL_AXIOMS`.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_bv_compute(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BV_SUB_SELF))
            .is_some()
        {
            return Ok(());
        }

        // Width-4 gate-fidelity layer (carrier/ops/eq/Bool-helpers) ...
        self.init_bv_compute_width(BV_COMPUTE_WIDTH)?;
        // ... plus the fully-PROVED non-reflexive width-4 identities (exponential
        // case split; NOT generalized — see module docs).
        self.register_bv4_theorems()?;
        Ok(())
    }

    /// Register the width-4 **machine-vs-IR fidelity** layer on top of
    /// [`Environment::init_bv_compute`]: a SEPARATELY-defined IR-side adder
    /// `bvAddIr` (right-associated sum `xor3Ir`, the `(a&&b)||(c&&(a||b))`
    /// majority `majIr` — both syntactically DIFFERENT terms from the machine
    /// `xor3`/`maj`) and the PROVED theorem
    /// `bvAdd_eq_ir : (x y : Clean.BV4) → bvEq (bvAdd x y) (bvAddIr x y)`.
    ///
    /// This is the rung-3 SUBSTRATE: a real output-preservation fidelity theorem
    /// (machine adder ≡ IR adder), registered as kernel `Expr`s reachable from
    /// `clean-auto` (clean-kernel only — no parser/elab/.lean), with an EMPTY
    /// domain-axiom closure, that the [`crate::proved_gate`]-style `Instantiated`
    /// path can instantiate.
    ///
    /// NON-VACUITY (the make-or-break point): `bvAdd` and `bvAddIr` are distinct
    /// `Definition`s (different per-bit sum/carry gates), so `bvEq (bvAdd x y)
    /// (bvAddIr x y)` is NOT closeable by `rfl` for symbolic `x`/`y`; the theorem
    /// DISCHARGES the gate-encoding difference by an exhaustive 2⁸-leaf `Bool.rec`
    /// case split (each ground leaf agrees because both adders compute the same
    /// value). A wrong-gate `bvAddIr` (e.g. dropping the carry) would make a leaf
    /// FALSE and the theorem unprovable — see the `bitvec_compute_tests` controls.
    ///
    /// Idempotent. # Errors: propagates any [`EnvError`] from declaration
    /// insertion / kernel checking (a non-fidelity IR adder fails to check here).
    pub fn init_bv_fidelity(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::BV_ADD_EQ_IR))
            .is_some()
        {
            return Ok(());
        }
        self.init_bv_compute()?;
        self.register_bv4_ir_adder()?;
        self.register_bv4_add_eq_ir()?;
        Ok(())
    }

    /// Register the computational width-`N` BitVec gate-fidelity layer:
    /// `Clean.BV{N}` carrier + `N` bit accessors, `bvZero`/`bvNot`, the `N`-bit
    /// ripple-carry `bvAdd`/`bvSub`, the `N`-conjunct `bvEq`, and the (shared,
    /// width-independent) `xor3`/`maj`/`xnor` primitives + Bool helper theorems.
    ///
    /// This is the layer the criterion-2 lowering bridge trusts to faithfully
    /// encode width-`N` `bvAdd`: each output bit `i` is `xor3(xᵢ, yᵢ, cᵢ)` with
    /// `cᵢ₊₁ = maj(xᵢ, yᵢ, cᵢ)`, so the kernel re-check of a width-`N` bit-blast
    /// reduces the actual width-`N` gate trees. It does NOT register the proved
    /// `bvAdd_comm`-style identities (those are exponential and width-4 only).
    ///
    /// Idempotent per width. Requires `Bool`, `Eq`, `And`, `True`, `Or`.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    /// Returns [`EnvError`] for `width == 0`.
    pub fn init_bv_compute_width(&mut self, width: u32) -> Result<(), EnvError> {
        let nm = BvNames::new(width);
        if width == 0 {
            return Err(EnvError::InvalidDeclarationShape {
                init: "init_bv_compute_width",
                decl: Name::from_string(&nm.bv()),
                detail: "width must be >= 1",
            });
        }
        if self.get_const(&Name::from_string(&nm.bv_eq())).is_some() {
            return Ok(());
        }

        self.init_eq()?;
        self.init_bool()?;
        self.init_and()?;
        self.init_true_false()?;

        self.register_bv_carrier(nm)?;
        self.register_bv_ops(nm)?;
        self.register_bv_eq(nm)?;
        self.register_bv4_bool_helpers()?; // width-independent; shared namespace
        Ok(())
    }

    // ── §1 carrier + bit accessors (width-N) ──────────────────────────────────

    fn register_bv_carrier(&mut self, nm: BvNames) -> Result<(), EnvError> {
        let n = nm.width;
        // inductive Clean.BV{N} where | mk (b0 .. b{N-1} : Bool) : Clean.BV{N}
        if self.get_inductive(&Name::from_string(&nm.bv())).is_none() {
            let bv_type = Expr::type_();
            let mk_type = {
                let mut b = EnvDeclBuilder::new();
                let ids: Vec<_> = (0..n).map(|_| b.fresh_local(bool_ty()).0).collect();
                let mut r = bv_ty_w(nm);
                for id in ids.into_iter().rev() {
                    r = b.mk_pi(id, BinderInfo::Default, bool_ty(), r);
                }
                b.finish(r)
            };
            let decl = InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string(&nm.bv()),
                    type_: bv_type,
                    constructors: vec![Constructor {
                        name: Name::from_string(&nm.bv_mk()),
                        type_: mk_type,
                    }],
                }],
            };
            self.add_inductive(decl)?;
        }

        // bit{k} v := Clean.BV{N}.rec (motive := fun _ => Bool)
        //              (fun b0 .. b{N-1} => b{k}) v
        // (mirrors core `Bool.not`/`Fin.val`: one-constructor recursor projection)
        let bv_rec = Expr::const_(
            Name::from_string(&format!("{}.rec", nm.bv())),
            vec![Level::succ(Level::zero())],
        );
        for k in 0u32..n {
            let acc_ty = Expr::arrow(bv_ty_w(nm), bool_ty());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (v_id, v) = b.fresh_local(bv_ty_w(nm));
                // motive : fun (_ : Clean.BV{N}) => Bool
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(bv_ty_w(nm));
                    c.finish_child(c.mk_lam(w_id, BinderInfo::Default, bv_ty_w(nm), bool_ty()))
                };
                // mk_case : fun (b0 .. b{N-1} : Bool) => b{k}
                let mk_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let bits: Vec<_> = (0..n).map(|_| c.fresh_local(bool_ty())).collect();
                    let chosen = bits[k as usize].1.clone();
                    let mut r = chosen;
                    for (id, _) in bits.into_iter().rev() {
                        r = c.mk_lam(id, BinderInfo::Default, bool_ty(), r);
                    }
                    c.finish_child(r)
                };
                let body = Expr::apps(bv_rec.clone(), [motive, mk_case, v]);
                let e = b.mk_lam(v_id, BinderInfo::Default, bv_ty_w(nm), body);
                b.finish(e)
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(&nm.bit(k)),
                level_params: vec![],
                type_: acc_ty,
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    // ── §1 reducible Boolean adder primitives + bvZero/Not/Add/Sub (width-N) ───

    fn register_bv_ops(&mut self, nm: BvNames) -> Result<(), EnvError> {
        let n = nm.width;
        // xor3 a b c := Bool.xor (Bool.xor a b) c
        let ternary_ty = Expr::arrow(
            bool_ty(),
            Expr::arrow(bool_ty(), Expr::arrow(bool_ty(), bool_ty())),
        );
        let xor3_value = ternary_lam(|a, b, c| bxor(bxor(a, b), c));
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::XOR3),
            level_params: vec![],
            type_: ternary_ty.clone(),
            value: xor3_value,
            is_reducible: true,
        })?;

        // maj a b c := Bool.or (Bool.and a b) (Bool.or (Bool.and a c) (Bool.and b c))
        let maj_value = ternary_lam(|a, b, c| {
            bor(
                band(a.clone(), b.clone()),
                bor(band(a, c.clone()), band(b, c)),
            )
        });
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::MAJ),
            level_params: vec![],
            type_: ternary_ty,
            value: maj_value,
            is_reducible: true,
        })?;

        // bvZero := mk false .. false   (N times)
        let zero_bits: Vec<Expr> = (0..n).map(|_| bfalse()).collect();
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(&nm.bv_zero()),
            level_params: vec![],
            type_: bv_ty_w(nm),
            value: bv_mk_w(nm, &zero_bits),
            is_reducible: true,
        })?;

        // bvNot v := mk (not (bit0 v)) .. (not (bit{N-1} v))
        let unop_ty = Expr::arrow(bv_ty_w(nm), bv_ty_w(nm));
        let bvnot_value = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(bv_ty_w(nm));
            let bits: Vec<Expr> = (0..n).map(|k| bnot(bit_w(nm, v.clone(), k))).collect();
            let body = bv_mk_w(nm, &bits);
            b.finish(b.mk_lam(v_id, BinderInfo::Default, bv_ty_w(nm), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(&nm.bv_not()),
            level_params: vec![],
            type_: unop_ty,
            value: bvnot_value,
            is_reducible: true,
        })?;

        // bvAdd x y := ripple-carry from carry-in false.
        // bvSub x y := ripple-carry of x, (not y) from carry-in true.
        let binop_ty = Expr::arrow(bv_ty_w(nm), Expr::arrow(bv_ty_w(nm), bv_ty_w(nm)));
        for (op_name, carry_in, complement_y) in
            [(nm.bv_add(), bfalse(), false), (nm.bv_sub(), btrue(), true)]
        {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(bv_ty_w(nm));
                let (y_id, y) = b.fresh_local(bv_ty_w(nm));
                let yb = |k: u32| {
                    if complement_y {
                        bnot(bit_w(nm, y.clone(), k))
                    } else {
                        bit_w(nm, y.clone(), k)
                    }
                };
                // ripple carry: c0 = carry_in; sum_k = xor3 xk yk ck; c_{k+1}=maj
                let mut carry = carry_in.clone();
                let mut sum_bits: Vec<Expr> = Vec::with_capacity(n as usize);
                for k in 0..n {
                    let xk = bit_w(nm, x.clone(), k);
                    let yk = yb(k);
                    sum_bits.push(xor3(xk.clone(), yk.clone(), carry.clone()));
                    // Only compute the next carry if there is a higher bit to consume it.
                    if k + 1 < n {
                        carry = maj(xk, yk, carry);
                    }
                }
                let body = bv_mk_w(nm, &sum_bits);
                let e = b.mk_lam(y_id, BinderInfo::Default, bv_ty_w(nm), body);
                let e = b.mk_lam(x_id, BinderInfo::Default, bv_ty_w(nm), e);
                b.finish(e)
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(&op_name),
                level_params: vec![],
                type_: binop_ty.clone(),
                value,
                is_reducible: true,
            })?;
        }

        // bvXor x y := mk (xor (bit0 x) (bit0 y)) .. (xor (bit{N-1} x) (bit{N-1} y))
        // Bitwise: NO carry chain — a different gate-fidelity than the adder. This is
        // the kernel image of the real GVN commutative-XOR canonicalization, so the
        // criterion-2 re-check of `bvEq (bvXor a b) (bvXor b a)` reduces the actual
        // per-bit `Bool.xor` gate trees (output bit i is `Bool.xor (bitᵢ x) (bitᵢ y)`).
        let bvxor_value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bv_ty_w(nm));
            let (y_id, y) = b.fresh_local(bv_ty_w(nm));
            let bits: Vec<Expr> = (0..n)
                .map(|k| bxor(bit_w(nm, x.clone(), k), bit_w(nm, y.clone(), k)))
                .collect();
            let body = bv_mk_w(nm, &bits);
            let e = b.mk_lam(y_id, BinderInfo::Default, bv_ty_w(nm), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, bv_ty_w(nm), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(&nm.bv_xor()),
            level_params: vec![],
            type_: binop_ty.clone(),
            value: bvxor_value,
            is_reducible: true,
        })?;

        // bvAnd x y := mk (and (bit0 x) (bit0 y)) .. (and (bit{N-1} x) (bit{N-1} y))
        // Bitwise: NO carry chain — a different gate-fidelity than the adder. This is
        // the kernel image of the real GVN commutative-AND canonicalization, so the
        // criterion-2 re-check of `bvEq (bvAnd a b) (bvAnd b a)` reduces the actual
        // per-bit `Bool.and` gate trees (output bit i is `Bool.and (bitᵢ x) (bitᵢ y)`).
        let bvand_value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bv_ty_w(nm));
            let (y_id, y) = b.fresh_local(bv_ty_w(nm));
            let bits: Vec<Expr> = (0..n)
                .map(|k| band(bit_w(nm, x.clone(), k), bit_w(nm, y.clone(), k)))
                .collect();
            let body = bv_mk_w(nm, &bits);
            let e = b.mk_lam(y_id, BinderInfo::Default, bv_ty_w(nm), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, bv_ty_w(nm), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(&nm.bv_and()),
            level_params: vec![],
            type_: binop_ty.clone(),
            value: bvand_value,
            is_reducible: true,
        })?;

        // bvOr x y := mk (or (bit0 x) (bit0 y)) .. (or (bit{N-1} x) (bit{N-1} y))
        // Bitwise: NO carry chain — a different gate-fidelity than the adder. This is
        // the kernel image of the real GVN commutative-OR canonicalization, so the
        // criterion-2 re-check of `bvEq (bvOr a b) (bvOr b a)` reduces the actual
        // per-bit `Bool.or` gate trees (output bit i is `Bool.or (bitᵢ x) (bitᵢ y)`).
        let bvor_value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bv_ty_w(nm));
            let (y_id, y) = b.fresh_local(bv_ty_w(nm));
            let bits: Vec<Expr> = (0..n)
                .map(|k| bor(bit_w(nm, x.clone(), k), bit_w(nm, y.clone(), k)))
                .collect();
            let body = bv_mk_w(nm, &bits);
            let e = b.mk_lam(y_id, BinderInfo::Default, bv_ty_w(nm), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, bv_ty_w(nm), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(&nm.bv_or()),
            level_params: vec![],
            type_: binop_ty,
            value: bvor_value,
            is_reducible: true,
        })?;
        Ok(())
    }

    // ── §1 bvEq : per-bit And-chain (definitional, width-N) ────────────────────

    fn register_bv_eq(&mut self, nm: BvNames) -> Result<(), EnvError> {
        // bvEq x y := And (bit0 x = bit0 y) (And (bit1 x = bit1 y) (And ... (bit{N-1} x = bit{N-1} y)))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bv_ty_w(nm));
            let (y_id, y) = b.fresh_local(bv_ty_w(nm));
            let body = bit_eq_and_chain_w(nm, &x, &y);
            let e = b.mk_lam(y_id, BinderInfo::Default, bv_ty_w(nm), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, bv_ty_w(nm), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(&nm.bv_eq()),
            level_params: vec![],
            type_: Expr::arrow(bv_ty_w(nm), Expr::arrow(bv_ty_w(nm), Expr::prop())),
            value,
            is_reducible: true,
        })?;
        Ok(())
    }

    // ── §1b Bool helper def + theorems (for the solver-backed replay) ─────────
    //
    // These back the zero-trust kernel replay of a SOLVER-DERIVED (non-identical)
    // bit-blast refutation: `boolEm` is Bool totality (resolution needs a literal
    // and its negation to be exhaustive), `eqTfElim` is the literal/negation
    // contradiction used at every resolution pivot, and `xnorTrueImpEq` discharges
    // the per-bit `XnorEq` equality from the bit-equality gate. All are proved by
    // `Bool.rec` case analysis; axiom closure ⊆ FOUNDATIONAL_AXIOMS.

    fn register_bv4_bool_helpers(&mut self) -> Result<(), EnvError> {
        self.init_or()?; // Or / Or.inl / Or.inr / Or.rec

        // xnor a b := Bool.not (Bool.xor a b)  — the bit-equality gate.
        let binary_ty = Expr::arrow(bool_ty(), Expr::arrow(bool_ty(), bool_ty()));
        let xnor_value = {
            let mut b = EnvDeclBuilder::new();
            let (i0, x) = b.fresh_local(bool_ty());
            let (i1, y) = b.fresh_local(bool_ty());
            let body = bnot(bxor(x, y));
            let e = b.mk_lam(i1, BinderInfo::Default, bool_ty(), body);
            b.finish(b.mk_lam(i0, BinderInfo::Default, bool_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::XNOR),
            level_params: vec![],
            type_: binary_ty,
            value: xnor_value,
            is_reducible: true,
        })?;

        self.register_bool_em()?;
        self.register_eq_tf_elim()?;
        self.register_xnor_true_imp_eq()?;
        self.register_lit_clash()?;
        self.register_not_false_imp_true()?;
        self.register_eq_imp_xnor_true()?;
        Ok(())
    }

    /// `eqImpXnorTrue : (x y : Bool) → Eq x y → Eq (xnor x y) true`.
    ///
    /// `Eq.rec` (substitute `y := x` in the goal `xnor x y = true`) reduces the goal
    /// to `xnor x x = true`; then `Bool.rec` on `x` makes `xnor x x` ι/δ-reduce to
    /// `true` in each leaf, closed by `Eq.refl`. Axiom closure ⊆ FOUNDATIONAL_AXIOMS.
    fn register_eq_imp_xnor_true(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::EQ_IMP_XNOR_TRUE))
            .is_some()
        {
            return Ok(());
        }
        let xnor = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::XNOR), [x, y]);
        let concl = |x: Expr, y: Expr| eq_bool(xnor(x, y), btrue());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(bool_ty());
            let (yid, y) = b.fresh_local(bool_ty());
            let inner = Expr::arrow(eq_bool(x.clone(), y.clone()), concl(x.clone(), y.clone()));
            let e = b.mk_pi(yid, BinderInfo::Default, bool_ty(), inner);
            b.finish(b.mk_pi(xid, BinderInfo::Default, bool_ty(), e))
        };
        // `xnorXX x : xnor x x = true` by Bool.rec on x (each leaf ≡ true → rfl).
        let xnor_xx = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(bool_ty());
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(bool_ty());
                c.finish_child(c.mk_lam(
                    mid,
                    BinderInfo::Default,
                    bool_ty(),
                    concl(m.clone(), m.clone()),
                ))
            };
            // false leaf: xnor false false ≡ true → Eq.refl true
            let f_case = eq_refl_bool(btrue());
            let t_case = eq_refl_bool(btrue());
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
            let body = Expr::apps(bool_rec, [motive, f_case, t_case, x.clone()]);
            b.finish(b.mk_lam(xid, BinderInfo::Default, bool_ty(), body))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(bool_ty());
            let (yid, y) = b.fresh_local(bool_ty());
            let (hid, h) = b.fresh_local(eq_bool(x.clone(), y.clone()));
            // motive for Eq.rec : fun (w:Bool) (_ : Eq x w) => xnor x w = true
            // Use @Eq.subst Bool (fun w => xnor x w = true) x y h (xnorXX x).
            let pred = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (wid, w) = c.fresh_local(bool_ty());
                c.finish_child(c.mk_lam(wid, BinderInfo::Default, bool_ty(), concl(x.clone(), w)))
            };
            let base = Expr::app(xnor_xx.clone(), x.clone());
            let eq_subst = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let body = Expr::apps(
                eq_subst,
                [bool_ty(), pred, x.clone(), y.clone(), h.clone(), base],
            );
            let r = b.mk_lam(
                hid,
                BinderInfo::Default,
                eq_bool(x.clone(), y.clone()),
                body,
            );
            let r = b.mk_lam(yid, BinderInfo::Default, bool_ty(), r);
            b.finish(b.mk_lam(xid, BinderInfo::Default, bool_ty(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::EQ_IMP_XNOR_TRUE),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `notFalseImpTrue : (b : Bool) → Eq b false → Eq (Bool.not b) true`.
    ///
    /// Case on `b`: at `b = false`, `Bool.not false ≡ true`, so the conclusion is
    /// `Eq.refl true`; at `b = true`, the hypothesis `true = false` is absurd
    /// (`tf_to_false`), discharged into the conclusion by `False.elim`. Proved by
    /// `Bool.rec`; axiom closure ⊆ FOUNDATIONAL_AXIOMS.
    fn register_not_false_imp_true(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::NOT_FALSE_IMP_TRUE))
            .is_some()
        {
            return Ok(());
        }
        let h_of = |b: Expr| eq_bool(b, bfalse());
        let concl_of = |b: Expr| eq_bool(bnot(b), btrue());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (bid, bb) = b.fresh_local(bool_ty());
            let inner = Expr::arrow(h_of(bb.clone()), concl_of(bb.clone()));
            b.finish(b.mk_pi(bid, BinderInfo::Default, bool_ty(), inner))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bid, bb) = b.fresh_local(bool_ty());
            // motive : fun (x:Bool) => (x=false) → (Bool.not x = true)
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(bool_ty());
                let body = Expr::arrow(h_of(m.clone()), concl_of(m.clone()));
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, bool_ty(), body))
            };
            // false branch: fun (_h:false=false) => Eq.refl true   (Bool.not false ≡ true)
            let false_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i, _h) = c.fresh_local(h_of(bfalse()));
                let body = eq_refl_bool(btrue());
                c.finish_child(c.mk_lam(i, BinderInfo::Default, h_of(bfalse()), body))
            };
            // true branch: fun (h:true=false) => False.elim (Bool.not true = true) (tf_to_false h)
            let true_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i, h) = c.fresh_local(h_of(btrue()));
                let contra = tf_to_false(h);
                let body = Expr::apps(
                    Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                    [concl_of(btrue()), contra],
                );
                c.finish_child(c.mk_lam(i, BinderInfo::Default, h_of(btrue()), body))
            };
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
            let body = Expr::apps(bool_rec, [motive, false_case, true_case, bb]);
            b.finish(b.mk_lam(bid, BinderInfo::Default, bool_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::NOT_FALSE_IMP_TRUE),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `litClash : (b : Bool) → Eq b true → Eq (Bool.not b) true → False`.
    ///
    /// Case on `b`: at `b = true`, the hypothesis `Bool.not true = true` reduces to
    /// `false = true` (absurd via `tf_to_false ∘ Eq.symm`); at `b = false`, the
    /// hypothesis `b = true` is `false = true` (absurd directly). Proved entirely by
    /// `Bool.rec`; axiom closure ⊆ FOUNDATIONAL_AXIOMS.
    fn register_lit_clash(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::LIT_CLASH))
            .is_some()
        {
            return Ok(());
        }
        let false_c = Expr::const_str("False");
        let h1_of = |b: Expr| eq_bool(b, btrue());
        let h2_of = |b: Expr| eq_bool(bnot(b), btrue());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (bid, bb) = b.fresh_local(bool_ty());
            let inner = Expr::arrow(h2_of(bb.clone()), false_c.clone());
            let inner = Expr::arrow(h1_of(bb.clone()), inner);
            b.finish(b.mk_pi(bid, BinderInfo::Default, bool_ty(), inner))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bid, bb) = b.fresh_local(bool_ty());
            // motive : fun (x:Bool) => (x=true) → (Bool.not x = true) → False
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(bool_ty());
                let body = Expr::arrow(h2_of(m.clone()), false_c.clone());
                let body = Expr::arrow(h1_of(m.clone()), body);
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, bool_ty(), body))
            };
            // false branch: fun (h1:false=true)(_h2) => tf_to_false (Eq.symm h1)
            let false_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i1, hh1) = c.fresh_local(h1_of(bfalse()));
                let (i2, _hh2) = c.fresh_local(h2_of(bfalse()));
                // Eq.symm hh1 : true = false
                let tf = eq_symm_bool(bfalse(), btrue(), hh1);
                let body = tf_to_false(tf);
                let r = c.mk_lam(i2, BinderInfo::Default, h2_of(bfalse()), body);
                c.finish_child(c.mk_lam(i1, BinderInfo::Default, h1_of(bfalse()), r))
            };
            // true branch: fun (_h1)(h2:Bool.not true = true) => tf_to_false (Eq.symm h2)
            // (Bool.not true ≡ false, so h2 : false = true; Eq.symm h2 : true = false.)
            let true_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i1, _hh1) = c.fresh_local(h1_of(btrue()));
                let (i2, hh2) = c.fresh_local(h2_of(btrue()));
                let tf = eq_symm_bool(bnot(btrue()), btrue(), hh2);
                let body = tf_to_false(tf);
                let r = c.mk_lam(i2, BinderInfo::Default, h2_of(btrue()), body);
                c.finish_child(c.mk_lam(i1, BinderInfo::Default, h1_of(btrue()), r))
            };
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
            let body = Expr::apps(bool_rec, [motive, false_case, true_case, bb]);
            b.finish(b.mk_lam(bid, BinderInfo::Default, bool_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::LIT_CLASH),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `boolEm : (b : Bool) → Or (Eq b true) (Eq b false)` by `Bool.rec`.
    fn register_bool_em(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(names::BOOL_EM)).is_some() {
            return Ok(());
        }
        let or =
            |p: Expr, q: Expr| Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [p, q]);
        let em_prop = |w: Expr| or(eq_bool(w.clone(), btrue()), eq_bool(w, bfalse()));
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (id, w) = b.fresh_local(bool_ty());
            b.finish(b.mk_pi(id, BinderInfo::Default, bool_ty(), em_prop(w)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (id, w) = b.fresh_local(bool_ty());
            // motive : fun (x:Bool) => Or (x=true) (x=false)
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(bool_ty());
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, bool_ty(), em_prop(m)))
            };
            // false-case : Or (false=true) (false=false) := Or.inr _ _ (rfl false)
            let false_case = or_inr(
                eq_bool(bfalse(), btrue()),
                eq_bool(bfalse(), bfalse()),
                eq_refl_bool(bfalse()),
            );
            // true-case : Or (true=true) (true=false) := Or.inl _ _ (rfl true)
            let true_case = or_inl(
                eq_bool(btrue(), btrue()),
                eq_bool(btrue(), bfalse()),
                eq_refl_bool(btrue()),
            );
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
            let body = Expr::apps(bool_rec, [motive, false_case, true_case, w]);
            b.finish(b.mk_lam(id, BinderInfo::Default, bool_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::BOOL_EM),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `eqTfElim : (b : Bool) → Eq b true → Eq b false → False`.
    ///
    /// Both `b = true` and `b = false` cannot hold: case on `b`; in each branch one
    /// hypothesis is `true = false` (or `false = true`), discharged by transporting
    /// `True.intro` along it into `False` via the `Bool.rec`-into-`Prop` predicate
    /// `P x := Bool.rec (fun _ => Prop) True False x` (`P true ≡ True`, `P false ≡ False`).
    fn register_eq_tf_elim(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::EQ_TF_ELIM))
            .is_some()
        {
            return Ok(());
        }
        let false_c = Expr::const_str("False");
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (bid, bb) = b.fresh_local(bool_ty());
            let h1 = eq_bool(bb.clone(), btrue());
            let h2 = eq_bool(bb.clone(), bfalse());
            let inner = Expr::arrow(h2, false_c.clone());
            let inner = Expr::arrow(h1, inner);
            b.finish(b.mk_pi(bid, BinderInfo::Default, bool_ty(), inner))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bid, bb) = b.fresh_local(bool_ty());
            // motive : fun (x:Bool) => (x=true) → (x=false) → False
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(bool_ty());
                let h1 = eq_bool(m.clone(), btrue());
                let h2 = eq_bool(m.clone(), bfalse());
                let body = Expr::arrow(h2, false_c.clone());
                let body = Expr::arrow(h1, body);
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, bool_ty(), body))
            };
            // false branch: fun (_h1:false=true)(_h2:false=false) => tfFalse (Eq.symm _h1)
            let false_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i1, hh1) = c.fresh_local(eq_bool(bfalse(), btrue()));
                let (i2, _hh2) = c.fresh_local(eq_bool(bfalse(), bfalse()));
                // Eq.symm hh1 : true = false
                let tf = eq_symm_bool(bfalse(), btrue(), hh1);
                let body = tf_to_false(tf);
                let r = c.mk_lam(i2, BinderInfo::Default, eq_bool(bfalse(), bfalse()), body);
                c.finish_child(c.mk_lam(i1, BinderInfo::Default, eq_bool(bfalse(), btrue()), r))
            };
            // true branch: fun (_h1:true=true)(h2:true=false) => tfFalse h2
            let true_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i1, _hh1) = c.fresh_local(eq_bool(btrue(), btrue()));
                let (i2, hh2) = c.fresh_local(eq_bool(btrue(), bfalse()));
                let body = tf_to_false(hh2);
                let r = c.mk_lam(i2, BinderInfo::Default, eq_bool(btrue(), bfalse()), body);
                c.finish_child(c.mk_lam(i1, BinderInfo::Default, eq_bool(btrue(), btrue()), r))
            };
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
            let body = Expr::apps(bool_rec, [motive, false_case, true_case, bb]);
            b.finish(b.mk_lam(bid, BinderInfo::Default, bool_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::EQ_TF_ELIM),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `xnorTrueImpEq : (x y : Bool) → Eq (xnor x y) true → Eq x y` by `Bool.rec`
    /// case analysis on `x`, `y` (4 ground leaves). At each leaf `xnor x y` reduces
    /// to a literal; the agreeing leaves close by `rfl`, the disagreeing leaves get
    /// `false = true` (an absurd hypothesis) discharged by `eqTfElim`.
    fn register_xnor_true_imp_eq(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::XNOR_TRUE_IMP_EQ))
            .is_some()
        {
            return Ok(());
        }
        let xnor = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::XNOR), [x, y]);
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(bool_ty());
            let (yid, y) = b.fresh_local(bool_ty());
            let hyp = eq_bool(xnor(x.clone(), y.clone()), btrue());
            let concl = eq_bool(x.clone(), y.clone());
            let inner = Expr::arrow(hyp, concl);
            let e = b.mk_pi(yid, BinderInfo::Default, bool_ty(), inner);
            b.finish(b.mk_pi(xid, BinderInfo::Default, bool_ty(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(bool_ty());
            let (yid, y) = b.fresh_local(bool_ty());
            // hyp/concl as a function of (gx, gy)
            let hyp_of = |gx: &Expr, gy: &Expr| eq_bool(xnor(gx.clone(), gy.clone()), btrue());
            let concl_of = |gx: &Expr, gy: &Expr| eq_bool(gx.clone(), gy.clone());

            // Inner builder over x: motive_x : fun (wx) => (y fixed) ... we nest y too.
            // We do nested Bool.rec: outer on x, inner on y, each leaf a lambda over
            // the hypothesis producing `concl`.
            let leaf = |gx: &Expr, gy: &Expr, parent: &EnvDeclBuilder| -> Expr {
                // fun (h : xnor gx gy = true) => proof of gx = gy
                let mut c = EnvDeclBuilder::child_of(parent);
                let (hid, h) = c.fresh_local(hyp_of(gx, gy));
                // If gx and gy are the same literal -> rfl; else absurd via eqTfElim.
                let body = ground_xnor_leaf(gx, gy, &h);
                c.finish_child(c.mk_lam(hid, BinderInfo::Default, hyp_of(gx, gy), body))
            };

            // motive over x: fun (wx:Bool) => (y:Bool fixed) hyp -> concl, but the y
            // and hyp are part of the result Pi (y already bound outside the rec on x).
            // We build: rec_x with motive fun wx => hyp_of(wx,y) -> concl_of(wx,y),
            // then inside each x-branch, rec_y with motive fun wy => hyp_of(x_lit,wy)->concl.
            let motive_x = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (mid, m) = c.fresh_local(bool_ty());
                let body = Expr::arrow(hyp_of(&m, &y), concl_of(&m, &y));
                c.finish_child(c.mk_lam(mid, BinderInfo::Default, bool_ty(), body))
            };
            let x_branch = |gx: &Expr, parent: &EnvDeclBuilder| -> Expr {
                // rec_y over y at fixed gx.
                let d = EnvDeclBuilder::child_of(parent);
                let motive_y = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (mid, m) = e.fresh_local(bool_ty());
                    let body = Expr::arrow(hyp_of(gx, &m), concl_of(gx, &m));
                    e.finish_child(e.mk_lam(mid, BinderInfo::Default, bool_ty(), body))
                };
                let y_false = leaf(gx, &bfalse(), &d);
                let y_true = leaf(gx, &btrue(), &d);
                let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
                d.finish_child(Expr::apps(bool_rec, [motive_y, y_false, y_true, y.clone()]))
            };
            let x_false = x_branch(&bfalse(), &b);
            let x_true = x_branch(&btrue(), &b);
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
            let body = Expr::apps(bool_rec, [motive_x, x_false, x_true, x.clone()]);
            let e = b.mk_lam(yid, BinderInfo::Default, bool_ty(), body);
            b.finish(b.mk_lam(xid, BinderInfo::Default, bool_ty(), e))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::XNOR_TRUE_IMP_EQ),
            level_params: vec![],
            type_,
            value,
        })
    }

    // ── §2 the proved kernel theorems ─────────────────────────────────────────

    fn register_bv4_theorems(&mut self) -> Result<(), EnvError> {
        // bvSub_self : (a : Clean.BV4) → bvEq (bvSub a a) bvZero
        let bv_zero = Expr::const_str(names::BV_ZERO);
        self.register_bv4_unary_identity(
            names::BV_SUB_SELF,
            |a| Expr::apps(Expr::const_str(names::BV_SUB), [a.clone(), a]),
            |_| bv_zero.clone(),
        )?;

        // bvAdd_zero : (a : Clean.BV4) → bvEq (bvAdd a bvZero) a
        let bv_zero2 = Expr::const_str(names::BV_ZERO);
        self.register_bv4_unary_identity(
            names::BV_ADD_ZERO,
            move |a| Expr::apps(Expr::const_str(names::BV_ADD), [a, bv_zero2.clone()]),
            |a| a,
        )?;

        // bvAdd_comm : (a b : Clean.BV4) → bvEq (bvAdd a b) (bvAdd b a)
        self.register_bv4_add_comm()?;
        Ok(())
    }

    /// Register the IR-side gates `xor3Ir`/`majIr` and the IR-side ripple adder
    /// `bvAddIr` — all reducible `Definition`s, SEPARATELY defined from the
    /// machine `xor3`/`maj`/`bvAdd` (right-assoc sum + a different majority term).
    fn register_bv4_ir_adder(&mut self) -> Result<(), EnvError> {
        let n = BV_COMPUTE_WIDTH;
        let nm = BvNames::new(n);
        let ternary_ty = Expr::arrow(
            bool_ty(),
            Expr::arrow(bool_ty(), Expr::arrow(bool_ty(), bool_ty())),
        );
        // xor3Ir a b c := Bool.xor a (Bool.xor b c)   (RIGHT-associated)
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::XOR3_IR),
            level_params: vec![],
            type_: ternary_ty.clone(),
            value: ternary_lam(|a, b, c| bxor(a, bxor(b, c))),
            is_reducible: true,
        })?;
        // majIr a b c := Bool.or (Bool.and a b) (Bool.and c (Bool.or a b))
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::MAJ_IR),
            level_params: vec![],
            type_: ternary_ty,
            value: ternary_lam(|a, b, c| bor(band(a.clone(), b.clone()), band(c, bor(a, b)))),
            is_reducible: true,
        })?;
        // bvAddIr x y := ripple-carry from carry-in false, using xor3Ir/majIr.
        let binop_ty = Expr::arrow(bv_ty_w(nm), Expr::arrow(bv_ty_w(nm), bv_ty_w(nm)));
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bv_ty_w(nm));
            let (y_id, y) = b.fresh_local(bv_ty_w(nm));
            let mut carry = bfalse();
            let mut sum_bits: Vec<Expr> = Vec::with_capacity(n as usize);
            for k in 0..n {
                let xk = bit_w(nm, x.clone(), k);
                let yk = bit_w(nm, y.clone(), k);
                sum_bits.push(xor3_ir(xk.clone(), yk.clone(), carry.clone()));
                if k + 1 < n {
                    carry = maj_ir(xk, yk, carry);
                }
            }
            let body = bv_mk_w(nm, &sum_bits);
            let e = b.mk_lam(y_id, BinderInfo::Default, bv_ty_w(nm), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, bv_ty_w(nm), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::BV_ADD_IR),
            level_params: vec![],
            type_: binop_ty,
            value,
            is_reducible: true,
        })?;
        Ok(())
    }

    /// Register `bvAdd_eq_ir : (x y : Clean.BV4) → bvEq (bvAdd x y) (bvAddIr x y)`,
    /// the machine-vs-IR adder FIDELITY theorem. Proved by the same 2⁸-leaf
    /// `Bool.rec` case split as `bvAdd_comm`: at every ground bit assignment both
    /// adders ι/δ-reduce to the SAME concrete BV4, so each per-bit conjunct closes
    /// by `Eq.refl`. NON-VACUOUS: `bvAdd` (machine `maj`/`xor3`) and `bvAddIr`
    /// (IR `majIr`/`xor3Ir`) are distinct terms, so the symbolic goal is not `rfl`.
    fn register_bv4_add_eq_ir(&mut self) -> Result<(), EnvError> {
        let thm = names::BV_ADD_EQ_IR;
        if self.get_const(&Name::from_string(thm)).is_some() {
            return Ok(());
        }
        let add_m = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::BV_ADD), [x, y]);
        let add_ir = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::BV_ADD_IR), [x, y]);
        let goal_of = |x: Expr, y: Expr| bv_eq(add_m(x.clone(), y.clone()), add_ir(x, y));

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bv_ty());
            let (y_id, y) = b.fresh_local(bv_ty());
            let concl = goal_of(x.clone(), y.clone());
            let e = b.mk_pi(y_id, BinderInfo::Default, bv_ty(), concl);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, bv_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(bv_ty());
            let (y_id, y) = b.fresh_local(bv_ty());
            // outer rec on x: motive (wx) = bvEq (add_m wx y) (add_ir wx y)
            let motive_x = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(bv_ty());
                c.finish_child(c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    bv_ty(),
                    goal_of(w.clone(), y.clone()),
                ))
            };
            let x_mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x0_id, x0) = c.fresh_local(bool_ty());
                let (x1_id, x1) = c.fresh_local(bool_ty());
                let (x2_id, x2) = c.fresh_local(bool_ty());
                let (x3_id, x3) = c.fresh_local(bool_ty());
                let xbits = [x0.clone(), x1.clone(), x2.clone(), x3.clone()];
                let inner = {
                    let d = EnvDeclBuilder::child_of(&c);
                    let xmk = bv_mk(xbits.clone());
                    let motive_y = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (w_id, w) = e.fresh_local(bv_ty());
                        e.finish_child(e.mk_lam(
                            w_id,
                            BinderInfo::Default,
                            bv_ty(),
                            goal_of(xmk.clone(), w),
                        ))
                    };
                    let y_mk_case = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (y0_id, y0) = e.fresh_local(bool_ty());
                        let (y1_id, y1) = e.fresh_local(bool_ty());
                        let (y2_id, y2) = e.fresh_local(bool_ty());
                        let (y3_id, y3) = e.fresh_local(bool_ty());
                        let all8 = [
                            xbits[0].clone(),
                            xbits[1].clone(),
                            xbits[2].clone(),
                            xbits[3].clone(),
                            y0.clone(),
                            y1.clone(),
                            y2.clone(),
                            y3.clone(),
                        ];
                        let goal = |g: [Expr; 8]| {
                            let xmk =
                                bv_mk([g[0].clone(), g[1].clone(), g[2].clone(), g[3].clone()]);
                            let ymk =
                                bv_mk([g[4].clone(), g[5].clone(), g[6].clone(), g[7].clone()]);
                            goal_of(xmk, ymk)
                        };
                        let proof = bool_case_split_8(&e, all8, &goal, &|g| {
                            let xmk =
                                bv_mk([g[0].clone(), g[1].clone(), g[2].clone(), g[3].clone()]);
                            let ymk =
                                bv_mk([g[4].clone(), g[5].clone(), g[6].clone(), g[7].clone()]);
                            ground_bv_eq_proof(
                                &|_| add_m(xmk.clone(), ymk.clone()),
                                &|_| add_ir(xmk.clone(), ymk.clone()),
                                xmk.clone(),
                            )
                        });
                        e.finish_child(e.mk_lam(
                            y0_id,
                            BinderInfo::Default,
                            bool_ty(),
                            e.mk_lam(
                                y1_id,
                                BinderInfo::Default,
                                bool_ty(),
                                e.mk_lam(
                                    y2_id,
                                    BinderInfo::Default,
                                    bool_ty(),
                                    e.mk_lam(y3_id, BinderInfo::Default, bool_ty(), proof),
                                ),
                            ),
                        ))
                    };
                    let y_rec = Expr::const_(
                        Name::from_string(&format!("{}.rec", names::BV)),
                        vec![Level::zero()],
                    );
                    d.finish_child(Expr::apps(y_rec, [motive_y, y_mk_case, y.clone()]))
                };
                c.finish_child(c.mk_lam(
                    x0_id,
                    BinderInfo::Default,
                    bool_ty(),
                    c.mk_lam(
                        x1_id,
                        BinderInfo::Default,
                        bool_ty(),
                        c.mk_lam(
                            x2_id,
                            BinderInfo::Default,
                            bool_ty(),
                            c.mk_lam(x3_id, BinderInfo::Default, bool_ty(), inner),
                        ),
                    ),
                ))
            };
            let x_rec = Expr::const_(
                Name::from_string(&format!("{}.rec", names::BV)),
                vec![Level::zero()],
            );
            let app = Expr::apps(x_rec, [motive_x, x_mk_case, x.clone()]);
            let e = b.mk_lam(y_id, BinderInfo::Default, bv_ty(), app);
            let e = b.mk_lam(x_id, BinderInfo::Default, bv_ty(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(thm),
            level_params: vec![],
            type_,
            value,
        })?;
        Ok(())
    }

    /// Register `thm : (a : Clean.BV4) → bvEq (lhs a) (rhs a)` proved by 4-way
    /// nested `Bool.rec` case analysis on `a`'s bits. For every ground bit
    /// assignment, both `lhs`/`rhs` reduce (ι/δ on the adder + accessors) so each
    /// per-bit conjunct's leaf is `Eq.refl` and the whole `bvEq` is `And.intro`s.
    fn register_bv4_unary_identity(
        &mut self,
        thm: &str,
        lhs: impl Fn(Expr) -> Expr,
        rhs: impl Fn(Expr) -> Expr,
    ) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(thm)).is_some() {
            return Ok(());
        }
        // type: (a : Clean.BV4) → bvEq (lhs a) (rhs a)
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bv_ty());
            let concl = bv_eq(lhs(a.clone()), rhs(a));
            b.finish(b.mk_pi(a_id, BinderInfo::Default, bv_ty(), concl))
        };
        // value: fun (a : Clean.BV4) => Clean.BV4.casesOn-on-mk via Clean.BV4.rec.
        // For the SINGLE constructor mk, we destructure `a` into ground bits
        // (each still symbolic Bool), then 4× nest Bool.rec on the bits so all
        // leaves are ground -> Eq.refl chains.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bv_ty());
            // motive over a : fun (w : Clean.BV4) => bvEq (lhs w) (rhs w)
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(bv_ty());
                c.finish_child(c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    bv_ty(),
                    bv_eq(lhs(w.clone()), rhs(w)),
                ))
            };
            let mk_case = self.bv4_mk_case_unary(&b, &lhs, &rhs);
            let bv_rec = Expr::const_(Name::from_string("Clean.BV4.rec"), vec![Level::zero()]);
            let body = Expr::apps(bv_rec, [motive, mk_case, a]);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, bv_ty(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(thm),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// The `mk` minor premise of the outer `Clean.BV4.rec` for a unary identity:
    /// binds 4 symbolic bits `a0..a3` then nests `Bool.rec` on each so the proof
    /// goal becomes ground at every leaf.
    fn bv4_mk_case_unary(
        &self,
        parent: &EnvDeclBuilder,
        lhs: &impl Fn(Expr) -> Expr,
        rhs: &impl Fn(Expr) -> Expr,
    ) -> Expr {
        let mut c = EnvDeclBuilder::child_of(parent);
        let (a0_id, a0) = c.fresh_local(bool_ty());
        let (a1_id, a1) = c.fresh_local(bool_ty());
        let (a2_id, a2) = c.fresh_local(bool_ty());
        let (a3_id, a3) = c.fresh_local(bool_ty());
        // goal at a fully/partly-ground bit vector `bits`:
        //   bvEq (lhs (mk bits)) (rhs (mk bits))
        let goal = |bits: [Expr; 4]| {
            let mkv = bv_mk(bits);
            bv_eq(lhs(mkv.clone()), rhs(mkv))
        };
        let proof = bool_case_split_4(
            &c,
            [a0.clone(), a1.clone(), a2.clone(), a3.clone()],
            &goal,
            &|bits| ground_bv_eq_proof(lhs, rhs, bv_mk(bits)),
        );
        let r = c.mk_lam(a3_id, BinderInfo::Default, bool_ty(), proof);
        let r = c.mk_lam(a2_id, BinderInfo::Default, bool_ty(), r);
        let r = c.mk_lam(a1_id, BinderInfo::Default, bool_ty(), r);
        let r = c.mk_lam(a0_id, BinderInfo::Default, bool_ty(), r);
        c.finish_child(r)
    }

    /// `bvAdd_comm : (a b : Clean.BV4) → bvEq (bvAdd a b) (bvAdd b a)` — nested
    /// `Bool.rec` over all 8 bits of `a` and `b` (256 ground leaves; each refl).
    fn register_bv4_add_comm(&mut self) -> Result<(), EnvError> {
        let thm = names::BV_ADD_COMM;
        if self.get_const(&Name::from_string(thm)).is_some() {
            return Ok(());
        }
        let add = |x: Expr, y: Expr| Expr::apps(Expr::const_str(names::BV_ADD), [x, y]);
        let goal_of = |x: Expr, y: Expr| bv_eq(add(x.clone(), y.clone()), add(y, x));

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bv_ty());
            let (bv_id, bvv) = b.fresh_local(bv_ty());
            let concl = goal_of(a.clone(), bvv.clone());
            let e = b.mk_pi(bv_id, BinderInfo::Default, bv_ty(), concl);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, bv_ty(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(bv_ty());
            let (bv_id, bvv) = b.fresh_local(bv_ty());

            // Destructure a via outer rec, then b via inner rec, then 8 Bool.recs.
            // motive_a : fun (wa : BV4) => bvEq (add wa b) (add b wa)
            let motive_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = c.fresh_local(bv_ty());
                c.finish_child(c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    bv_ty(),
                    goal_of(w.clone(), bvv.clone()),
                ))
            };
            let a_mk_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a0_id, a0) = c.fresh_local(bool_ty());
                let (a1_id, a1) = c.fresh_local(bool_ty());
                let (a2_id, a2) = c.fresh_local(bool_ty());
                let (a3_id, a3) = c.fresh_local(bool_ty());
                let abits = [a0.clone(), a1.clone(), a2.clone(), a3.clone()];
                // inner rec on b
                let inner = {
                    let d = EnvDeclBuilder::child_of(&c);
                    let amk = bv_mk(abits.clone());
                    let motive_b = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (w_id, w) = e.fresh_local(bv_ty());
                        e.finish_child(e.mk_lam(
                            w_id,
                            BinderInfo::Default,
                            bv_ty(),
                            goal_of(amk.clone(), w),
                        ))
                    };
                    let b_mk_case = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (b0_id, b0) = e.fresh_local(bool_ty());
                        let (b1_id, b1) = e.fresh_local(bool_ty());
                        let (b2_id, b2) = e.fresh_local(bool_ty());
                        let (b3_id, b3) = e.fresh_local(bool_ty());
                        let bbits = [b0.clone(), b1.clone(), b2.clone(), b3.clone()];
                        // 8-way split: a0..a3 then b0..b3.
                        let goal = |g: [Expr; 8]| {
                            let amk =
                                bv_mk([g[0].clone(), g[1].clone(), g[2].clone(), g[3].clone()]);
                            let bmk =
                                bv_mk([g[4].clone(), g[5].clone(), g[6].clone(), g[7].clone()]);
                            goal_of(amk, bmk)
                        };
                        let all8 = [
                            abits[0].clone(),
                            abits[1].clone(),
                            abits[2].clone(),
                            abits[3].clone(),
                            bbits[0].clone(),
                            bbits[1].clone(),
                            bbits[2].clone(),
                            bbits[3].clone(),
                        ];
                        let proof = bool_case_split_8(&e, all8, &goal, &|g| {
                            let amk =
                                bv_mk([g[0].clone(), g[1].clone(), g[2].clone(), g[3].clone()]);
                            let bmk =
                                bv_mk([g[4].clone(), g[5].clone(), g[6].clone(), g[7].clone()]);
                            // prove bvEq (add amk bmk) (add bmk amk) by refl-chain
                            ground_bv_eq_proof(
                                &|_| add(amk.clone(), bmk.clone()),
                                &|_| add(bmk.clone(), amk.clone()),
                                amk.clone(),
                            )
                        });
                        let r = e.mk_lam(b3_id, BinderInfo::Default, bool_ty(), proof);
                        let r = e.mk_lam(b2_id, BinderInfo::Default, bool_ty(), r);
                        let r = e.mk_lam(b1_id, BinderInfo::Default, bool_ty(), r);
                        let r = e.mk_lam(b0_id, BinderInfo::Default, bool_ty(), r);
                        e.finish_child(r)
                    };
                    let bv_rec =
                        Expr::const_(Name::from_string("Clean.BV4.rec"), vec![Level::zero()]);
                    d.finish_child(Expr::apps(bv_rec, [motive_b, b_mk_case, bvv.clone()]))
                };
                let r = c.mk_lam(a3_id, BinderInfo::Default, bool_ty(), inner);
                let r = c.mk_lam(a2_id, BinderInfo::Default, bool_ty(), r);
                let r = c.mk_lam(a1_id, BinderInfo::Default, bool_ty(), r);
                let r = c.mk_lam(a0_id, BinderInfo::Default, bool_ty(), r);
                c.finish_child(r)
            };
            let bv_rec = Expr::const_(Name::from_string("Clean.BV4.rec"), vec![Level::zero()]);
            let outer = Expr::apps(bv_rec, [motive_a, a_mk_case, a.clone()]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, bv_ty(), outer);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, bv_ty(), e))
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(thm),
            level_params: vec![],
            type_,
            value,
        })
    }
}

// ── free helpers ──────────────────────────────────────────────────────────────

/// `@Or.inl a b ha`.
fn or_inl(a: Expr, b: Expr, ha: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Or.inl"), vec![]),
        [a, b, ha],
    )
}
/// `@Or.inr a b hb`.
fn or_inr(a: Expr, b: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Or.inr"), vec![]),
        [a, b, hb],
    )
}
/// `@Eq.refl.{1} Bool x : Eq x x`.
fn eq_refl_bool(x: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [bool_ty(), x],
    )
}
/// `@Eq.symm.{1} Bool a b h : Eq b a`.
fn eq_symm_bool(a: Expr, b: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![u1]),
        [bool_ty(), a, b, h],
    )
}
/// `htf : Eq Bool.true Bool.false → False` by transporting `True.intro` along the
/// `Bool.rec`-into-`Prop` predicate `P x := Bool.rec (fun _ => Prop) True False x`
/// (`P true ≡ True`, `P false ≡ False`) via `Eq.subst`.
fn tf_to_false(htf: Expr) -> Expr {
    // P := fun (x:Bool) => @Bool.rec (fun _ => Prop) True False x : Bool → Prop
    let p = {
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        // motive of the inner rec: fun (_:Bool) => Prop
        let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), Expr::prop());
        let body = Expr::apps(
            bool_rec,
            [
                inner_motive,
                Expr::const_str("False"),
                Expr::const_str("True"),
                Expr::bvar(0),
            ],
        );
        Expr::lam(BinderInfo::Default, bool_ty(), body)
    };
    // @Eq.subst.{1} Bool P true false htf (True.intro) : P false ≡ False
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(
        eq_subst,
        [
            bool_ty(),
            p,
            btrue(),
            bfalse(),
            htf,
            Expr::const_str("True.intro"),
        ],
    )
}
/// Proof of `Eq gx gy` from `h : Eq (xnor gx gy) Bool.true`, where `gx`/`gy` are
/// the ground bit literals. Agreeing leaves close by `rfl`; disagreeing leaves
/// have `xnor gx gy ≡ false`, so `h : false = true` is absurd (via `eqTfElim`).
fn ground_xnor_leaf(gx: &Expr, gy: &Expr, h: &Expr) -> Expr {
    if gx == gy {
        return eq_refl_bool(gx.clone());
    }
    // eqTfElim Bool.false h (Eq.refl false) : False   (h : false = true up to defeq)
    let elim = Expr::apps(
        Expr::const_str(names::EQ_TF_ELIM),
        [bfalse(), h.clone(), eq_refl_bool(bfalse())],
    );
    // False.elim.{0} (Eq gx gy) elim
    Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [eq_bool(gx.clone(), gy.clone()), elim],
    )
}

/// `fun (a b c : Bool) => f a b c`.
fn ternary_lam(f: impl Fn(Expr, Expr, Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (i0, a) = b.fresh_local(bool_ty());
    let (i1, bb) = b.fresh_local(bool_ty());
    let (i2, c) = b.fresh_local(bool_ty());
    let body = f(a, bb, c);
    let e = b.mk_lam(i2, BinderInfo::Default, bool_ty(), body);
    let e = b.mk_lam(i1, BinderInfo::Default, bool_ty(), e);
    let e = b.mk_lam(i0, BinderInfo::Default, bool_ty(), e);
    b.finish(e)
}

/// `And (bit0 x = bit0 y) (And … (bit{N-1} x = bit{N-1} y))` — right-associated,
/// width-`N`. With `N == 1` the chain is the bare `bit0 x = bit0 y`.
fn bit_eq_and_chain_w(nm: BvNames, x: &Expr, y: &Expr) -> Expr {
    let and = |l: Expr, r: Expr| Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [l, r]);
    let n = nm.width;
    let conj = |k: u32| eq_bool(bit_w(nm, x.clone(), k), bit_w(nm, y.clone(), k));
    let mut acc = conj(n - 1);
    for k in (0..n - 1).rev() {
        acc = and(conj(k), acc);
    }
    acc
}

/// Proof of `bvEq (lhs v) (rhs v)` when `v` is a GROUND `mk` of literal bits:
/// the right-assoc `And.intro` chain of per-bit `Eq.refl`s. Sound because, with
/// all bits ground, the kernel ι/δ-reduces `lhs v`/`rhs v` to identical ground
/// bit vectors, so `Eq.refl (bitK (lhs v))` checks against `bitK (lhs v) = bitK (rhs v)`.
fn ground_bv_eq_proof(lhs: &impl Fn(Expr) -> Expr, rhs: &impl Fn(Expr) -> Expr, v: Expr) -> Expr {
    let lv = lhs(v.clone());
    let rv = rhs(v);
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
    let refl = |k: u32| Expr::apps(eq_refl.clone(), [bool_ty(), bit(lv.clone(), k)]);
    let eq_k = |k: u32| eq_bool(bit(lv.clone(), k), bit(rv.clone(), k));
    let and = |l: Expr, r: Expr| Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [l, r]);
    // chain bits 0..3 right-assoc, matching bvEq body shape.
    let p3 = refl(3);
    let t3 = eq_k(3);
    let p2 = Expr::apps(and_intro.clone(), [eq_k(2), t3.clone(), refl(2), p3]);
    let t2 = and(eq_k(2), t3);
    let p1 = Expr::apps(and_intro.clone(), [eq_k(1), t2.clone(), refl(1), p2]);
    let t1 = and(eq_k(1), t2);
    Expr::apps(and_intro, [eq_k(0), t1, refl(0), p1])
}

/// Nested `Bool.rec` over 4 symbolic bits `[a0,a1,a2,a3]`; at each ground leaf,
/// `leaf(bits)` provides the proof of `goal(bits)`. `goal`/`leaf` receive the
/// (partly ground) bit array.
fn bool_case_split_4(
    builder: &EnvDeclBuilder,
    bits: [Expr; 4],
    goal: &impl Fn([Expr; 4]) -> Expr,
    leaf: &impl Fn([Expr; 4]) -> Expr,
) -> Expr {
    rec_split(
        builder,
        &bits,
        &|ground| {
            let arr: [Expr; 4] = [
                ground[0].clone(),
                ground[1].clone(),
                ground[2].clone(),
                ground[3].clone(),
            ];
            leaf(arr)
        },
        &|ground| {
            let arr: [Expr; 4] = [
                ground[0].clone(),
                ground[1].clone(),
                ground[2].clone(),
                ground[3].clone(),
            ];
            goal(arr)
        },
    )
}

/// Nested `Bool.rec` over 8 symbolic bits.
fn bool_case_split_8(
    builder: &EnvDeclBuilder,
    bits: [Expr; 8],
    goal: &impl Fn([Expr; 8]) -> Expr,
    leaf: &impl Fn([Expr; 8]) -> Expr,
) -> Expr {
    rec_split(
        builder,
        &bits,
        &|g| {
            let a: [Expr; 8] = std::array::from_fn(|i| g[i].clone());
            leaf(a)
        },
        &|g| {
            let a: [Expr; 8] = std::array::from_fn(|i| g[i].clone());
            goal(a)
        },
    )
}

/// Generic nested `Bool.rec` over `bits[0..]`, substituting Bool.false/Bool.true
/// for each in turn. `leaf` is called with the fully-ground assignment; `goal`
/// computes the motive body at any (partly ground) assignment.
fn rec_split(
    builder: &EnvDeclBuilder,
    bits: &[Expr],
    leaf: &dyn Fn(&[Expr]) -> Expr,
    goal: &dyn Fn(&[Expr]) -> Expr,
) -> Expr {
    fn go(
        parent: &EnvDeclBuilder,
        prefix: &mut Vec<Expr>,
        rest: &[Expr],
        leaf: &dyn Fn(&[Expr]) -> Expr,
        goal: &dyn Fn(&[Expr]) -> Expr,
    ) -> Expr {
        if rest.is_empty() {
            return leaf(prefix);
        }
        let head = &rest[0];
        let tail = &rest[1..];
        let c = EnvDeclBuilder::child_of(parent);
        // motive : fun (w : Bool) => goal(prefix ++ [w] ++ remaining-symbolic-tail)
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&c);
            let (w_id, w) = d.fresh_local(bool_ty());
            let mut assign: Vec<Expr> = prefix.clone();
            assign.push(w);
            assign.extend_from_slice(tail);
            let body = goal(&assign);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, bool_ty(), body))
        };
        // false branch
        prefix.push(bfalse());
        let fb = go(&c, prefix, tail, leaf, goal);
        prefix.pop();
        // true branch
        prefix.push(btrue());
        let tb = go(&c, prefix, tail, leaf, goal);
        prefix.pop();
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        c.finish_child(Expr::apps(bool_rec, [motive, fb, tb, head.clone()]))
    }
    let mut prefix = Vec::with_capacity(bits.len());
    go(builder, &mut prefix, bits, leaf, goal)
}

#[cfg(test)]
#[path = "bitvec_compute_tests.rs"]
mod tests;
