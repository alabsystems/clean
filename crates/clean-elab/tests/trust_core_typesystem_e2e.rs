// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TrustCore: the Trust-Rust verification fragment, formalized AS Clean types.
//!
//! ## What this is
//!
//! Trust is a self-proving Rust compiler whose verifier reasons about a core
//! fragment of Rust (booleans + fixed-width bitvectors + the operations the
//! safety obligations are stated over). This file gives that fragment a
//! *formal type system and operational semantics inside Clean's CIC*:
//!
//!   - `TrustCore.Ty`  — the object-language types (`bool`, `bv w`).
//!   - `TrustCore.Den` — the denotation of each type as a Clean type.
//!   - `TrustCore.Tm`  — *intrinsically-typed* terms, indexed by their `Ty`.
//!     Because the syntax is intrinsically typed, "well-typed" is the only
//!     thing the inductive admits, so there are no ill-typed terms to get
//!     stuck on.
//!   - `TrustCore.eval` — a *total* evaluator `(t : Ty) → Tm t → Den t`. Its
//!     totality and type-indexed return type ARE type-soundness (progress +
//!     preservation) by construction: every well-typed term evaluates to a
//!     value of its denoted type, and the function is defined on every
//!     constructor.
//!
//! ## The soundness gate this enforces
//!
//! Per Clean's proof-soundness rule, "proved" means the theorem's transitive
//! axiom closure is `⊆ FOUNDATIONAL_AXIOMS` (propext, Quot.sound,
//! Classical.choice, + kernel primitives). `Environment::axiom_deps` returns
//! exactly the NON-foundational part of that closure (and includes any trust
//! marker), so `axiom_deps(thm).is_empty()` is the machine statement
//! "`thm` is proven all the way down to the foundational axioms."
//!
//! Every semantic theorem below is asserted to clear that gate. This is the
//! first installment of "all of Trust expressed as Clean types proven down to
//! the foundational axioms": the type system and its metatheorems are Clean
//! `Theorem`s with empty `axiom_deps`.

use clean_kernel::env::Environment;
use clean_kernel::Name;

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_parser::parse_file;

/// The TrustCore object language, in Clean surface (Lean 4) syntax.
const TRUSTCORE_SOURCE: &str = r#"
namespace TrustCore

-- The object-language types of the Trust-Rust verification fragment.
inductive Ty where
  | bool : Ty
  | bv : Nat -> Ty
  | nat : Ty
  | unit : Ty
  | prod : Ty -> Ty -> Ty
  | sum : Ty -> Ty -> Ty
  | opt : Ty -> Ty

-- Denotation of a TrustCore type as a Clean type. A bitvector of width `w` is
-- carried as a `Nat`; the unbounded `nat` type denotes `Nat` directly. Defined
-- via explicit `Ty.casesOn` (not equations) so `Den Ty.bool`/`Den (Ty.bv w)`/
-- `Den Ty.nat` reduce by iota during recursor minor-premise checking (required
-- by `eval`). Case order follows the constructors: bool, bv, nat.
def Den : Ty -> Type := fun t => @Ty.rec (fun _ => Type) Bool (fun _ => Nat) Nat Unit (fun _a _b Da Db => Prod Da Db) (fun _a _b Da Db => Sum Da Db) (fun _a Da => Option Da) t

-- Intrinsically-typed TrustCore terms, indexed by their TrustCore type. Because
-- the syntax is intrinsically typed, only well-typed terms are representable —
-- there are no ill-typed terms for the semantics to get stuck on.
inductive Tm : Ty -> Type where
  | tt : Tm Ty.bool
  | ff : Tm Ty.bool
  | lit : (w : Nat) -> Nat -> Tm (Ty.bv w)
  | band : Tm Ty.bool -> Tm Ty.bool -> Tm Ty.bool
  | add : (w : Nat) -> Tm (Ty.bv w) -> Tm (Ty.bv w) -> Tm (Ty.bv w)
  | ite : (t : Ty) -> Tm Ty.bool -> Tm t -> Tm t -> Tm t
  | ult : (w : Nat) -> Tm (Ty.bv w) -> Tm (Ty.bv w) -> Tm Ty.bool
  | bnot : Tm Ty.bool -> Tm Ty.bool
  | land : (w : Nat) -> Tm (Ty.bv w) -> Tm (Ty.bv w) -> Tm (Ty.bv w)
  | lor : (w : Nat) -> Tm (Ty.bv w) -> Tm (Ty.bv w) -> Tm (Ty.bv w)
  | lxor : (w : Nat) -> Tm (Ty.bv w) -> Tm (Ty.bv w) -> Tm (Ty.bv w)
  | sub : (w : Nat) -> Tm (Ty.bv w) -> Tm (Ty.bv w) -> Tm (Ty.bv w)
  | nlit : Nat -> Tm Ty.nat
  | nadd : Tm Ty.nat -> Tm Ty.nat -> Tm Ty.nat
  | nmul : Tm Ty.nat -> Tm Ty.nat -> Tm Ty.nat
  | nle : Tm Ty.nat -> Tm Ty.nat -> Tm Ty.bool
  | bor : Tm Ty.bool -> Tm Ty.bool -> Tm Ty.bool
  | bxor : Tm Ty.bool -> Tm Ty.bool -> Tm Ty.bool
  | u : Tm Ty.unit
  | mul : (w : Nat) -> Tm (Ty.bv w) -> Tm (Ty.bv w) -> Tm (Ty.bv w)
  | nsub : Tm Ty.nat -> Tm Ty.nat -> Tm Ty.nat
  | pair : (a b : Ty) -> Tm a -> Tm b -> Tm (Ty.prod a b)
  | fst : (a b : Ty) -> Tm (Ty.prod a b) -> Tm a
  | snd : (a b : Ty) -> Tm (Ty.prod a b) -> Tm b
  | inl : (a b : Ty) -> Tm a -> Tm (Ty.sum a b)
  | inr : (a b : Ty) -> Tm b -> Tm (Ty.sum a b)
  | some : (a : Ty) -> Tm a -> Tm (Ty.opt a)
  | none : (a : Ty) -> Tm (Ty.opt a)

-- Operation semantics over the unsigned modular carrier (value reduced
-- `% 2 ^ w`), matching clean's BitVec `Fin (2 ^ w)` representation. These are
-- the operations the Trust verifier's safety obligations are stated over.
def bvadd (w a b : Nat) : Nat := (a + b) % (2 ^ w)

-- Modular subtraction: add the additive inverse of `b` (`2^w - b mod 2^w`), so
-- the result is `(a - b) mod 2^w` with no Nat truncation (the inverse is always
-- positive since `b mod 2^w < 2^w`).
def bvsub (w a b : Nat) : Nat := (a + (2 ^ w - b % (2 ^ w))) % (2 ^ w)

-- Unsigned less-than as a proposition over the modular carrier.
def Bvult (w a b : Nat) : Prop := Nat.lt (a % (2 ^ w)) (b % (2 ^ w))

-- Metatheorem (the semantic ground of the milestone-1 `bvult`-antisymmetry
-- certification): unsigned less-than is irreflexive — `a <u a` is impossible at
-- every width. The Trust verifier's antisymmetry refutation
-- (`(a <u b) ∧ (b <u a) -> False`) rests on exactly this fact. Proven
-- constructively from `Nat.lt_irrefl`, no domain axioms.
theorem bvult_irrefl (w a : Nat) : Bvult w a a -> False :=
  Nat.lt_irrefl (a % (2 ^ w))

-- Bitwise operations over the carrier (Trust's `bvand`/`bvor`/`bvxor`), modelled
-- by the kernel's `Nat.land`/`Nat.lor`/`Nat.xor`.
def bvand (a b : Nat) : Nat := Nat.land a b
def bvor (a b : Nat) : Nat := Nat.lor a b
def bvxor (a b : Nat) : Nat := Nat.xor a b
def bvmul (w a b : Nat) : Nat := (Nat.mul a b) % (2 ^ w)

-- Metatheorems (the semantic ground of bit-blasted bitwise reasoning): each
-- bitwise op agrees with its boolean connective BIT BY BIT — the per-gate
-- adequacy law a certified bit-blaster needs to lift a BitVec operation to its
-- boolean-circuit encoding. Proven constructively from the kernel's
-- `Nat.testBit_and/or/xor` (constructive corollaries of `Nat.testBit_bitwise`).
theorem bvand_testBit (a b i : Nat) :
    Nat.testBit (bvand a b) i = (Nat.testBit a i && Nat.testBit b i) :=
  Nat.testBit_and a b i

theorem bvor_testBit (a b i : Nat) :
    Nat.testBit (bvor a b) i = (Nat.testBit a i || Nat.testBit b i) :=
  Nat.testBit_or a b i

theorem bvxor_testBit (a b i : Nat) :
    Nat.testBit (bvxor a b) i = Bool.xor (Nat.testBit a i) (Nat.testBit b i) :=
  Nat.testBit_xor a b i

-- Metatheorem (THE milestone-1 obligation itself): unsigned less-than is
-- asymmetric — `(a <u b) ∧ (b <u a)` is contradictory at every width. This is
-- exactly the proposition the Trust verifier refutes when it certifies a
-- `bvult`-antisymmetry VC. Proven constructively from `Nat.lt_asymm`; no domain
-- axioms.
theorem bvult_asymm (w a b : Nat) : Bvult w a b -> Bvult w b a -> False :=
  fun h1 h2 => Nat.lt_asymm (a % (2 ^ w)) (b % (2 ^ w)) h1 h2

-- Metatheorem: unsigned less-than is transitive — completes the order triad
-- (irreflexive, asymmetric, transitive) the verifier's chained-comparison
-- reasoning relies on. Proven constructively by `Nat.le_of_lt` then
-- `Nat.lt_of_le_of_lt`; no domain axioms.
theorem bvult_trans (w a b c : Nat) : Bvult w a b -> Bvult w b c -> Bvult w a c :=
  fun h1 h2 =>
    Nat.lt_of_le_of_lt (a % (2 ^ w)) (b % (2 ^ w)) (c % (2 ^ w))
      (Nat.le_of_lt h1)
      h2

-- Metatheorem: bitvector addition is commutative at every width — a basic
-- algebraic law of the modular `bvadd` semantics. Proven constructively by
-- congruence on `Nat.add_comm`; no domain axioms.
theorem bvadd_comm (w a b : Nat) : bvadd w a b = bvadd w b a :=
  congrArg (fun n => n % (2 ^ w)) (Nat.add_comm a b)

-- Metatheorems: bitwise AND/OR are commutative at every width. Proven by BIT
-- EXTENSIONALITY (`Nat.eq_of_testBit_eq`): two carriers are equal iff equal at
-- every bit, and bit `i` of `bvand a b` is `(bit a) && (bit b)` = `(bit b) &&
-- (bit a)` = bit `i` of `bvand b a` (by `Bool.and_comm`). This is the structural
-- shape of bit-blasted equality reasoning; no domain axioms.
theorem bvand_comm (a b : Nat) : bvand a b = bvand b a :=
  Nat.eq_of_testBit_eq (Nat.land a b) (Nat.land b a)
    (fun i =>
      Eq.trans (Nat.testBit_and a b i)
        (Eq.trans (Bool.and_comm (Nat.testBit a i) (Nat.testBit b i))
          (Eq.symm (Nat.testBit_and b a i))))

theorem bvor_comm (a b : Nat) : bvor a b = bvor b a :=
  Nat.eq_of_testBit_eq (Nat.lor a b) (Nat.lor b a)
    (fun i =>
      Eq.trans (Nat.testBit_or a b i)
        (Eq.trans (Bool.or_comm (Nat.testBit a i) (Nat.testBit b i))
          (Eq.symm (Nat.testBit_or b a i))))

theorem bvxor_comm (a b : Nat) : bvxor a b = bvxor b a :=
  Nat.eq_of_testBit_eq (Nat.xor a b) (Nat.xor b a)
    (fun i =>
      Eq.trans (Nat.testBit_xor a b i)
        (Eq.trans (Bool.xor_comm (Nat.testBit a i) (Nat.testBit b i))
          (Eq.symm (Nat.testBit_xor b a i))))

-- Dynamic semantics: the TOTAL evaluator, via the kernel recursor `@Tm.rec` with
-- the explicit dependent motive `fun t _ => Den t` and the per-constructor
-- induction hypotheses (NO equation-compiler recursion, so no `brecOn` to
-- mis-type). Now that `Den` reduces by iota (casesOn form), each minor premise
-- type-checks. Totality + the type-indexed codomain ARE type soundness (progress
-- + preservation) by construction: no ill-typed term can get stuck, and `eval`
-- is total over every constructor.
def eval (t : Ty) (e : Tm t) : Den t :=
  @Tm.rec
    (fun t _ => Den t)
    true
    false
    (fun w n => n % (2 ^ w))
    (fun _x _x1 ihx ihx1 => Bool.and ihx ihx1)
    (fun w _x _x1 ihx ihx1 => (ihx + ihx1) % (2 ^ w))
    (fun _t _x _x1 _x2 ihx ihx1 ihx2 => match ihx with | true => ihx1 | false => ihx2)
    (fun _w _x _x1 ihx ihx1 => decide (Nat.lt ihx ihx1))
    (fun _x ihx => Bool.not ihx)
    (fun _w _x _x1 ihx ihx1 => Nat.land ihx ihx1)
    (fun _w _x _x1 ihx ihx1 => Nat.lor ihx ihx1)
    (fun _w _x _x1 ihx ihx1 => Nat.xor ihx ihx1)
    (fun w _x _x1 ihx ihx1 => bvsub w ihx ihx1)
    (fun n => n)
    (fun _x _x1 ihx ihx1 => Nat.add ihx ihx1)
    (fun _x _x1 ihx ihx1 => Nat.mul ihx ihx1)
    (fun _x _x1 ihx ihx1 => decide (Nat.le ihx ihx1))
    (fun _x _x1 ihx ihx1 => Bool.or ihx ihx1)
    (fun _x _x1 ihx ihx1 => Bool.xor ihx ihx1)
    Unit.unit
    (fun w _x _x1 ihx ihx1 => bvmul w ihx ihx1)
    (fun _x _x1 ihx ihx1 => Nat.sub ihx ihx1)
    (fun a b _x _y ihx ihy => @Prod.mk (Den a) (Den b) ihx ihy)
    (fun a b _p ihp => @Prod.fst (Den a) (Den b) ihp)
    (fun a b _p ihp => @Prod.snd (Den a) (Den b) ihp)
    (fun a b _x ihx => @Sum.inl (Den a) (Den b) ihx)
    (fun a b _y ihy => @Sum.inr (Den a) (Den b) ihy)
    (fun a _x ihx => @Option.some (Den a) ihx)
    (fun a => @Option.none (Den a))
    t e

-- Metatheorem: `band tt b` evaluates the same as `b` (left identity of the
-- modelled conjunction), by iota-reduction of `Tm.rec` and `Bool.and`.
theorem eval_band_tt (b : Tm Ty.bool) :
    eval Ty.bool (Tm.band Tm.tt b) = eval Ty.bool b := rfl

-- Metatheorem: `band ff b` evaluates to `false` (left zero of conjunction).
theorem eval_band_ff (b : Tm Ty.bool) :
    eval Ty.bool (Tm.band Tm.ff b) = false := rfl

-- Metatheorem: an `ite` with a `tt` guard takes the `then` branch, at ANY result
-- type — a genuinely dependent statement (`t : Ty`, `x y : Tm t`).
theorem eval_ite_tt (t : Ty) (x y : Tm t) :
    eval t (Tm.ite t Tm.tt x y) = eval t x := rfl

-- Metatheorem: an `ite` with an `ff` guard takes the `else` branch.
theorem eval_ite_ff (t : Ty) (x y : Tm t) :
    eval t (Tm.ite t Tm.ff x y) = eval t y := rfl

-- Coherence metatheorems: the INTRINSIC term semantics (`eval` over `Tm`) agrees
-- with the standalone OPERATION semantics. The term-level `add`/`lit` evaluate
-- to exactly the `bvadd`/modular-literal the Trust verifier reasons about — so
-- the two layers are provably the same computation. Hold by `Tm.rec` iota.
theorem eval_add (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.add w x y) = bvadd w (eval (Ty.bv w) x) (eval (Ty.bv w) y) := rfl

theorem eval_lit (w n : Nat) :
    eval (Ty.bv w) (Tm.lit w n) = n % (2 ^ w) := rfl

-- Coherence: the first-class unsigned-comparison TERM `ult` evaluates to the
-- DECIDED unsigned `<` of its operands' values — so the verifier's core
-- comparison is expressible as a TrustCore term whose semantics is exactly the
-- decision procedure. Holds by `Tm.rec` iota.
theorem eval_ult (w : Nat) (x y : Tm (Ty.bv w)) :
    eval Ty.bool (Tm.ult w x y)
      = decide (Nat.lt (eval (Ty.bv w) x) (eval (Ty.bv w) y)) := rfl

-- Boolean double-negation involution (self-proven; the prelude does not
-- register `Bool.not_not`).
theorem bnot_bnot (x : Bool) : Bool.not (Bool.not x) = x :=
  match x with | true => rfl | false => rfl

-- Metatheorem (a semantic optimization law at the TERM level): double negation
-- of a boolean program term is the identity — `bnot (bnot b)` evaluates exactly
-- as `b`. By `Tm.rec` iota, `eval (bnot (bnot b))` reduces to
-- `Bool.not (Bool.not (eval b))`, closed by `bnot_bnot`.
theorem eval_bnot_bnot (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bnot (Tm.bnot b)) = eval Ty.bool b :=
  bnot_bnot (eval Ty.bool b)

-- TERM-level commutativity laws, lifting the already-proven operation laws to
-- the language's terms via `eval` iota (the `_self`/`_idem` variants are below,
-- after their `band_self`/`bvand_idem` helpers are in scope).
theorem eval_band_comm (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.band a b) = eval Ty.bool (Tm.band b a) :=
  Bool.and_comm (eval Ty.bool a) (eval Ty.bool b)

theorem eval_land_comm (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.land w x y) = eval (Ty.bv w) (Tm.land w y x) :=
  bvand_comm (eval (Ty.bv w) x) (eval (Ty.bv w) y)

theorem eval_lor_comm (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.lor w x y) = eval (Ty.bv w) (Tm.lor w y x) :=
  bvor_comm (eval (Ty.bv w) x) (eval (Ty.bv w) y)

theorem eval_lxor_comm (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.lxor w x y) = eval (Ty.bv w) (Tm.lxor w y x) :=
  bvxor_comm (eval (Ty.bv w) x) (eval (Ty.bv w) y)

theorem eval_add_comm (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.add w x y) = eval (Ty.bv w) (Tm.add w y x) :=
  bvadd_comm w (eval (Ty.bv w) x) (eval (Ty.bv w) y)

-- Coherence for the boolean-negation and bitvector-bitwise TERMS: each evaluates
-- to its operation-level counterpart applied to the operands' values, so the
-- term layer and the op layer are the same computation. Hold by `Tm.rec` iota.
theorem eval_bnot (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bnot b) = Bool.not (eval Ty.bool b) := rfl

theorem eval_land (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.land w x y) = bvand (eval (Ty.bv w) x) (eval (Ty.bv w) y) := rfl

theorem eval_lor (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.lor w x y) = bvor (eval (Ty.bv w) x) (eval (Ty.bv w) y) := rfl

theorem eval_lxor (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.lxor w x y) = bvxor (eval (Ty.bv w) x) (eval (Ty.bv w) y) := rfl

theorem eval_sub (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.sub w x y) = bvsub w (eval (Ty.bv w) x) (eval (Ty.bv w) y) := rfl

-- Bool idempotence helpers, proven by `Bool.rec` case analysis (both cases hold
-- by `rfl`); the prelude does not register these.
theorem band_self (b : Bool) : Bool.and b b = b := match b with | true => rfl | false => rfl
theorem bor_self (b : Bool) : Bool.or b b = b := match b with | true => rfl | false => rfl

-- Boolean conjunction associativity, self-proven (the prelude does not register
-- `Bool.and_assoc`). `Bool.and` recurses on its FIRST argument, so casing on `a`
-- alone makes both sides reduce: `a = true` ⇒ both `Bool.and b c`; `a = false`
-- ⇒ both `false`. So each case is `rfl`.
theorem band_assoc3 (a b c : Bool) :
    Bool.and (Bool.and a b) c = Bool.and a (Bool.and b c) :=
  match a with | true => rfl | false => rfl

-- Metatheorems: bitwise AND/OR are idempotent (`x & x = x`, `x | x = x`), proven
-- by bit extensionality + Bool idempotence. No domain axioms.
theorem bvand_idem (a : Nat) : bvand a a = a :=
  Nat.eq_of_testBit_eq (Nat.land a a) a
    (fun i => Eq.trans (Nat.testBit_and a a i) (band_self (Nat.testBit a i)))

theorem bvor_idem (a : Nat) : bvor a a = a :=
  Nat.eq_of_testBit_eq (Nat.lor a a) a
    (fun i => Eq.trans (Nat.testBit_or a a i) (bor_self (Nat.testBit a i)))

-- TERM-level idempotence laws (the `_self`/`_idem` variants), now that their
-- `band_self`/`bvand_idem` helpers are in scope. A verified compiler uses these
-- to collapse `b && b -> b` and `x &&& x -> x` on program terms.
theorem eval_band_self (b : Tm Ty.bool) :
    eval Ty.bool (Tm.band b b) = eval Ty.bool b :=
  band_self (eval Ty.bool b)

theorem eval_land_idem (w : Nat) (x : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.land w x x) = eval (Ty.bv w) x :=
  bvand_idem (eval (Ty.bv w) x)

theorem eval_lor_idem (w : Nat) (x : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.lor w x x) = eval (Ty.bv w) x :=
  bvor_idem (eval (Ty.bv w) x)

-- Unbounded-`nat` fragment: coherence of the nat literal/add/mul/le TERMS with
-- the underlying `Nat` operations (by `Tm.rec` iota).
theorem eval_nlit (n : Nat) : eval Ty.nat (Tm.nlit n) = n := rfl

theorem eval_nadd (x y : Tm Ty.nat) :
    eval Ty.nat (Tm.nadd x y) = Nat.add (eval Ty.nat x) (eval Ty.nat y) := rfl

theorem eval_nmul (x y : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul x y) = Nat.mul (eval Ty.nat x) (eval Ty.nat y) := rfl

theorem eval_nle (x y : Tm Ty.nat) :
    eval Ty.bool (Tm.nle x y) = decide (Nat.le (eval Ty.nat x) (eval Ty.nat y)) := rfl

-- New theorem class unlocked by the unbounded `nat` type: ASSOCIATIVITY (the
-- bitvector ops can't get this cleanly because of the `% 2^w` wrap). `nat`
-- addition is commutative AND associative at the term level.
theorem eval_nadd_comm (x y : Tm Ty.nat) :
    eval Ty.nat (Tm.nadd x y) = eval Ty.nat (Tm.nadd y x) :=
  Nat.add_comm (eval Ty.nat x) (eval Ty.nat y)

theorem eval_nadd_assoc (x y z : Tm Ty.nat) :
    eval Ty.nat (Tm.nadd (Tm.nadd x y) z) = eval Ty.nat (Tm.nadd x (Tm.nadd y z)) :=
  Nat.add_assoc (eval Ty.nat x) (eval Ty.nat y) (eval Ty.nat z)

-- Term-level boolean conjunction associativity (rewrite law) via `band_assoc3`.
theorem eval_band_assoc (a b c : Tm Ty.bool) :
    eval Ty.bool (Tm.band (Tm.band a b) c) = eval Ty.bool (Tm.band a (Tm.band b c)) :=
  band_assoc3 (eval Ty.bool a) (eval Ty.bool b) (eval Ty.bool c)

-- Nat additive identity at the term level: `0 + x` evaluates as `x` (via the
-- confirmed `Nat.zero_add`; `Nat.add_zero` is NOT in the prelude).
theorem eval_nadd_zero_left (x : Tm Ty.nat) :
    eval Ty.nat (Tm.nadd (Tm.nlit 0) x) = eval Ty.nat x :=
  Nat.zero_add (eval Ty.nat x)

-- Boolean OR/XOR fragment: coherence of the `bor`/`bxor` TERMS with `Bool.or`/
-- `Bool.xor`, plus the full law set. `Bool.or` recurses on its first argument,
-- so `bor_assoc3` cases on `a` alone (both reduce to rfl).
theorem eval_bor (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor a b) = Bool.or (eval Ty.bool a) (eval Ty.bool b) := rfl

theorem eval_bxor (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.bxor a b) = Bool.xor (eval Ty.bool a) (eval Ty.bool b) := rfl

theorem eval_bor_comm (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor a b) = eval Ty.bool (Tm.bor b a) :=
  Bool.or_comm (eval Ty.bool a) (eval Ty.bool b)

theorem eval_bxor_comm (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.bxor a b) = eval Ty.bool (Tm.bxor b a) :=
  Bool.xor_comm (eval Ty.bool a) (eval Ty.bool b)

theorem eval_bor_self (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor b b) = eval Ty.bool b :=
  bor_self (eval Ty.bool b)

theorem bor_assoc3 (a b c : Bool) :
    Bool.or (Bool.or a b) c = Bool.or a (Bool.or b c) :=
  match a with | true => rfl | false => rfl

theorem eval_bor_assoc (a b c : Tm Ty.bool) :
    eval Ty.bool (Tm.bor (Tm.bor a b) c) = eval Ty.bool (Tm.bor a (Tm.bor b c)) :=
  bor_assoc3 (eval Ty.bool a) (eval Ty.bool b) (eval Ty.bool c)

-- Bitvector bitwise ASSOCIATIVITY via bit extensionality + the boolean
-- associativity helpers + congruence on `Bool.and`/`Bool.or`. Rewriting the
-- nested `testBit (land a b) i` term uses `congrArg`. This is the full
-- bit-blasted equational reasoning chain a certified bit-blaster performs.
theorem bvand_assoc (a b c : Nat) : bvand (bvand a b) c = bvand a (bvand b c) :=
  Nat.eq_of_testBit_eq (Nat.land (Nat.land a b) c) (Nat.land a (Nat.land b c))
    (fun i =>
      Eq.trans (Nat.testBit_and (Nat.land a b) c i)
        (Eq.trans (congrArg (fun z => Bool.and z (Nat.testBit c i)) (Nat.testBit_and a b i))
          (Eq.trans (band_assoc3 (Nat.testBit a i) (Nat.testBit b i) (Nat.testBit c i))
            (Eq.trans
              (congrArg (fun z => Bool.and (Nat.testBit a i) z)
                (Eq.symm (Nat.testBit_and b c i)))
              (Eq.symm (Nat.testBit_and a (Nat.land b c) i))))))

theorem bvor_assoc (a b c : Nat) : bvor (bvor a b) c = bvor a (bvor b c) :=
  Nat.eq_of_testBit_eq (Nat.lor (Nat.lor a b) c) (Nat.lor a (Nat.lor b c))
    (fun i =>
      Eq.trans (Nat.testBit_or (Nat.lor a b) c i)
        (Eq.trans (congrArg (fun z => Bool.or z (Nat.testBit c i)) (Nat.testBit_or a b i))
          (Eq.trans (bor_assoc3 (Nat.testBit a i) (Nat.testBit b i) (Nat.testBit c i))
            (Eq.trans
              (congrArg (fun z => Bool.or (Nat.testBit a i) z)
                (Eq.symm (Nat.testBit_or b c i)))
              (Eq.symm (Nat.testBit_or a (Nat.lor b c) i))))))

-- Lifted to term-level rewrites.
theorem eval_land_assoc (w : Nat) (x y z : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.land w (Tm.land w x y) z)
      = eval (Ty.bv w) (Tm.land w x (Tm.land w y z)) :=
  bvand_assoc (eval (Ty.bv w) x) (eval (Ty.bv w) y) (eval (Ty.bv w) z)

theorem eval_lor_assoc (w : Nat) (x y z : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.lor w (Tm.lor w x y) z)
      = eval (Ty.bv w) (Tm.lor w x (Tm.lor w y z)) :=
  bvor_assoc (eval (Ty.bv w) x) (eval (Ty.bv w) y) (eval (Ty.bv w) z)

-- Boolean XOR self-cancellation (self-proven; the prelude lacks `Bool.xor_self`).
theorem bxor_self (x : Bool) : Bool.xor x x = false :=
  match x with | true => rfl | false => rfl

-- TERM-level XOR self-cancellation: `b XOR b` evaluates to `false` — a key
-- boolean optimization law, here about the language's own `bxor` term.
theorem eval_bxor_self (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bxor b b) = false :=
  bxor_self (eval Ty.bool b)

-- Nat multiplication theory, self-proven by induction (the prelude has NO mul
-- lemmas). `Nat.mul` recurses on its 2nd arg (mul x 0 = 0, mul x (succ y) =
-- mul x y + x), and `Nat.add x 0 = x` definitionally, so `mul 0 (succ k)`
-- reduces to `mul 0 k`; the successor case is exactly the IH.
theorem nmul_zero_left (n : Nat) : Nat.mul 0 n = 0 :=
  @Nat.rec (fun k => Nat.mul 0 k = 0) rfl (fun _ ih => ih) n

theorem eval_nmul_zero_left (x : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul (Tm.nlit 0) x) = 0 :=
  nmul_zero_left (eval Ty.nat x)


-- Nat multiplication theory, self-proven by @Nat.rec induction. The prelude has
-- NO multiplication lemmas, so the whole algebra is built from the definitional
-- reductions of `Nat.mul` (recurses on its 2nd arg: `mul x 0 = 0`,
-- `mul x (succ y) = Nat.add (mul x y) x`) and `Nat.add` (recurses on its 2nd
-- arg: `add x 0 = x`, `add x (succ y) = succ (add x y)`), combined with the
-- confirmed-constructive `Nat.add_assoc` / `Nat.add_comm`. (`nmul_zero_left`
-- and `eval_nmul_zero_left` are already in scope above.)

-- Right-commutativity of three-fold addition: `(a + b) + c = (a + c) + b`.
-- Pure `Nat.add_assoc` / `Nat.add_comm` / `congrArg` chain (no induction, no
-- domain axioms) -- the same equational style as `bvand_assoc` above.
theorem add_right_comm (a b c : Nat) :
    Nat.add (Nat.add a b) c = Nat.add (Nat.add a c) b :=
  Eq.trans (Nat.add_assoc a b c)
    (Eq.trans (congrArg (fun z => Nat.add a z) (Nat.add_comm b c))
      (Eq.symm (Nat.add_assoc a c b)))

-- `mul (succ a) n = (mul a n) + n`, by `@Nat.rec` on `n`. Base case `n = 0`:
-- both sides reduce to `0` (`mul (succ a) 0 = 0`, `add (mul a 0) 0 = add 0 0 =
-- 0`), so `rfl`. Step case `n = succ k` with `ih : mul (succ a) k = add (mul a
-- k) k`: the goal `motive (succ k)` is, after the definitional reductions of
-- `Nat.mul`/`Nat.add`, `add (mul (succ a) k) (succ a) = succ (add (add (mul a
-- k) a) k)`. Rewriting the LHS by `ih` (under `fun z => add z (succ a)`) and
-- the residual by `add_right_comm (mul a k) k a` (under `Nat.succ`) closes it.
theorem nmul_succ_left (a n : Nat) :
    Nat.mul (Nat.succ a) n = Nat.add (Nat.mul a n) n :=
  @Nat.rec
    (fun k => Nat.mul (Nat.succ a) k = Nat.add (Nat.mul a k) k)
    rfl
    (fun k ih =>
      Eq.trans
        (congrArg (fun z => Nat.add z (Nat.succ a)) ih)
        (congrArg (fun z => Nat.succ z) (add_right_comm (Nat.mul a k) k a)))
    n

-- Commutativity of `Nat.mul`, by `@Nat.rec` on `b`. Base `b = 0`: `mul a 0 = 0`
-- definitionally, and `Eq.symm (nmul_zero_left a) : 0 = mul 0 a` (the already-
-- proven left-zero helper). Step `b = succ k` with `ih : mul a k = mul k a`:
-- `mul a (succ k)` reduces to `add (mul a k) a`; rewrite by `ih` under
-- `fun z => add z a`, then close with `Eq.symm (nmul_succ_left k a)`.
theorem nmul_comm (a b : Nat) : Nat.mul a b = Nat.mul b a :=
  @Nat.rec
    (fun k => Nat.mul a k = Nat.mul k a)
    (Eq.symm (nmul_zero_left a))
    (fun k ih =>
      Eq.trans
        (congrArg (fun z => Nat.add z a) ih)
        (Eq.symm (nmul_succ_left k a)))
    b

-- Left identity of multiplication: `1 * n = n`, by `@Nat.rec` on `n`. `1`
-- expands to `Nat.succ Nat.zero` during kernel conversion (nat literal -> ctor
-- form), so `mul 1 (succ k) = add (mul 1 k) 1 = succ (mul 1 k)` definitionally;
-- the step is `congrArg Nat.succ ih`. Base `n = 0`: `mul 1 0 = 0`, `rfl`.
theorem nmul_one_left (n : Nat) : Nat.mul 1 n = n :=
  @Nat.rec
    (fun k => Nat.mul 1 k = k)
    rfl
    (fun k ih => congrArg (fun z => Nat.succ z) ih)
    n

-- TERM-level commutativity of TrustCore `nmul`: the program term `nmul x y`
-- evaluates exactly as `nmul y x`. By `Tm.rec` iota, `eval (nmul x y)` reduces
-- to `Nat.mul (eval x) (eval y)`, closed by `nmul_comm`. A verified compiler
-- uses this to commute multiplication operands on `nat` program terms.
theorem eval_nmul_comm (x y : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul x y) = eval Ty.nat (Tm.nmul y x) :=
  nmul_comm (eval Ty.nat x) (eval Ty.nat y)

-- Extra Nat addition laws over the unbounded `nat` carrier. The right-identity
-- and right-successor laws hold DEFINITIONALLY (`Nat.add` recurses on its second
-- argument: `add n 0 ≡ n`, `add a (succ b) ≡ succ (add a b)`), so each is `rfl`.
theorem nadd_zero_right (n : Nat) : Nat.add n 0 = n := rfl

theorem nadd_succ_right (a b : Nat) :
    Nat.add a (Nat.succ b) = Nat.succ (Nat.add a b) := rfl

-- Left-successor law. NOT definitional (add recurses on the SECOND arg), so it is
-- derived from `Nat.add_comm` + the definitional right-successor reduction:
--   add (succ a) b = add b (succ a)        [Nat.add_comm]
--                  ≡ succ (add b a)         [iota: add recurses on 2nd arg]
--                  = succ (add a b)         [congrArg succ (Nat.add_comm b a)].
theorem nadd_succ_left (a b : Nat) :
    Nat.add (Nat.succ a) b = Nat.succ (Nat.add a b) :=
  Eq.trans (Nat.add_comm (Nat.succ a) b)
    (congrArg (fun n => Nat.succ n) (Nat.add_comm b a))

-- Right-commutativity (`(a + b) + c = (a + c) + b`), via associativity then
-- commutativity of the inner pair then de-associativity:
--   (a + b) + c = a + (b + c)               [Nat.add_assoc]
--             = a + (c + b)                 [congrArg on Nat.add_comm b c]
--             = (a + c) + b                 [Eq.symm Nat.add_assoc].
theorem nadd_right_comm (a b c : Nat) :
    Nat.add (Nat.add a b) c = Nat.add (Nat.add a c) b :=
  Eq.trans (Nat.add_assoc a b c)
    (Eq.trans (congrArg (fun z => Nat.add a z) (Nat.add_comm b c))
      (Eq.symm (Nat.add_assoc a c b)))

-- TERM-level lifts via `eval` iota. `eval (nlit 0)` reduces to `0`, so
-- `eval (nadd x (nlit 0))` reduces (Tm.rec iota on `nadd`) to `Nat.add (eval x) 0`,
-- closed by `nadd_zero_right`.
theorem eval_nadd_zero_right (x : Tm Ty.nat) :
    eval Ty.nat (Tm.nadd x (Tm.nlit 0)) = eval Ty.nat x :=
  nadd_zero_right (eval Ty.nat x)

-- Term-level right-commutativity of `nadd`: both sides reduce (Tm.rec iota) to the
-- nested `Nat.add` form `nadd_right_comm` equates.
theorem eval_nadd_right_comm (x y z : Tm Ty.nat) :
    eval Ty.nat (Tm.nadd (Tm.nadd x y) z) = eval Ty.nat (Tm.nadd (Tm.nadd x z) y) :=
  nadd_right_comm (eval Ty.nat x) (eval Ty.nat y) (eval Ty.nat z)

-- Boolean De Morgan + absorption + unit laws, self-proven (the prelude does not
-- register Bool.and_assoc / Bool.not_and / absorption). `Bool.and`/`Bool.or`
-- recurse on their FIRST argument and `Bool.not` on its argument, so a single
-- `match` on the head variable makes BOTH sides reduce to the same normal form,
-- closing each case by `rfl`. Verified against the kernel definitions:
--   Bool.and a b = Bool.rec _ false b a   (false=>false, true=>b)
--   Bool.or  a b = Bool.rec _ b true a    (false=>b, true=>true)
--   Bool.not b   = Bool.rec _ true false b
theorem demorgan_and (a b : Bool) :
    Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) :=
  match a with | true => rfl | false => rfl

theorem demorgan_or (a b : Bool) :
    Bool.not (Bool.or a b) = Bool.and (Bool.not a) (Bool.not b) :=
  match a with | true => rfl | false => rfl

-- Absorption: a single case on `a` suffices because `Bool.and`/`Bool.or` reduce
-- by their first argument. `a = true`: `and true (or true b) = or true b = true`;
-- `a = false`: `and false _ = false`. Symmetric for `or`.
theorem absorb_and (a b : Bool) : Bool.and a (Bool.or a b) = a :=
  match a with | true => rfl | false => rfl

theorem absorb_or (a b : Bool) : Bool.or a (Bool.and a b) = a :=
  match a with | true => rfl | false => rfl

-- Right unit/zero laws for Bool.and/Bool.or (the prelude only computes the LEFT
-- cases by definitional unfolding; the right cases need a case on `b`).
theorem band_true (b : Bool) : Bool.and b true = b :=
  match b with | true => rfl | false => rfl

theorem band_false (b : Bool) : Bool.and b false = false :=
  match b with | true => rfl | false => rfl

theorem bor_false (b : Bool) : Bool.or b false = b :=
  match b with | true => rfl | false => rfl

theorem bor_true (b : Bool) : Bool.or b true = true :=
  match b with | true => rfl | false => rfl

-- TERM-level lifts: each Bool law lifted to TrustCore program terms via `eval`
-- iota. `eval (bnot x) = Bool.not (eval x)`, `eval (band a b) = Bool.and ..`,
-- `eval (bor a b) = Bool.or ..`, and `eval tt = true`/`eval ff = false`, so the
-- Bool-level helper's type matches the term goal up to defeq. A verified
-- compiler uses these to rewrite `!(a && b) -> !a || !b`, `a && (a || b) -> a`,
-- and `b && true -> b` on program terms.
theorem eval_demorgan_and (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.bnot (Tm.band a b))
      = eval Ty.bool (Tm.bor (Tm.bnot a) (Tm.bnot b)) :=
  demorgan_and (eval Ty.bool a) (eval Ty.bool b)

theorem eval_demorgan_or (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.bnot (Tm.bor a b))
      = eval Ty.bool (Tm.band (Tm.bnot a) (Tm.bnot b)) :=
  demorgan_or (eval Ty.bool a) (eval Ty.bool b)

theorem eval_absorb_and (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.band a (Tm.bor a b)) = eval Ty.bool a :=
  absorb_and (eval Ty.bool a) (eval Ty.bool b)

theorem eval_absorb_or (a b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor a (Tm.band a b)) = eval Ty.bool a :=
  absorb_or (eval Ty.bool a) (eval Ty.bool b)

theorem eval_band_true (b : Tm Ty.bool) :
    eval Ty.bool (Tm.band b Tm.tt) = eval Ty.bool b :=
  band_true (eval Ty.bool b)

theorem eval_band_false (b : Tm Ty.bool) :
    eval Ty.bool (Tm.band b Tm.ff) = false :=
  band_false (eval Ty.bool b)

theorem eval_bor_false (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor b Tm.ff) = eval Ty.bool b :=
  bor_false (eval Ty.bool b)

theorem eval_bor_true (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor b Tm.tt) = true :=
  bor_true (eval Ty.bool b)

-- Right-unit / right-zero helpers for `Bool.and` / `Bool.or`. Both connectives
-- recurse on their FIRST argument (`and a b := Bool.rec false b a`,
-- `or a b := Bool.rec b true a`), so casing on `b` alone makes each side reduce
-- to `rfl`. The prelude registers none of these.
theorem band_ff_right (b : Bool) : Bool.and b false = false :=
  match b with | true => rfl | false => rfl
theorem band_tt_right (b : Bool) : Bool.and b true = b :=
  match b with | true => rfl | false => rfl
theorem bor_ff_right (b : Bool) : Bool.or b false = b :=
  match b with | true => rfl | false => rfl
theorem bor_tt_right (b : Bool) : Bool.or b true = true :=
  match b with | true => rfl | false => rfl

-- Metatheorem: bitvector XOR self-cancellation (`x ^ x = 0`) at the carrier
-- level, proven by BIT EXTENSIONALITY: bit `i` of `Nat.xor a a` is
-- `Bool.xor (bit a) (bit a) = false` (by `bxor_self`), which is exactly bit `i`
-- of `0` (by the registered `Nat.testBit_zero_eq_false`). No domain axioms.
theorem bvxor_self (a : Nat) : bvxor a a = 0 :=
  Nat.eq_of_testBit_eq (Nat.xor a a) 0
    (fun i =>
      Eq.trans (Nat.testBit_xor a a i)
        (Eq.trans (bxor_self (Nat.testBit a i))
          (Eq.symm (Nat.testBit_zero_eq_false i))))

-- TERM-level XOR self-cancellation over the language's `lxor`: `x XOR x` on a
-- bitvector program term evaluates to `0` — the bit-blaster's `x ^ x -> 0`
-- rewrite, here about TrustCore's own `Tm.lxor`. By `Tm.rec` iota
-- `eval (lxor x x)` reduces to `bvxor (eval x) (eval x)`, closed by `bvxor_self`.
theorem eval_lxor_self (w : Nat) (x : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.lxor w x x) = 0 :=
  bvxor_self (eval (Ty.bv w) x)

-- TERM-level boolean right-identity / right-zero laws (a verified compiler uses
-- these to collapse `b && ff -> ff`, `b && tt -> b`, `b || ff -> b`,
-- `b || tt -> tt` on program terms). By `Tm.rec` iota, `eval (band b ff)`
-- reduces to `Bool.and (eval b) false`, etc., closed by the helpers above.
theorem eval_band_ff_right (b : Tm Ty.bool) :
    eval Ty.bool (Tm.band b Tm.ff) = false :=
  band_ff_right (eval Ty.bool b)

theorem eval_band_tt_right (b : Tm Ty.bool) :
    eval Ty.bool (Tm.band b Tm.tt) = eval Ty.bool b :=
  band_tt_right (eval Ty.bool b)

theorem eval_bor_ff_right (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor b Tm.ff) = eval Ty.bool b :=
  bor_ff_right (eval Ty.bool b)

theorem eval_bor_tt_right (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bor b Tm.tt) = true :=
  bor_tt_right (eval Ty.bool b)

-- Metatheorem (an `ite` collapse / branch-coalescing optimization at the TERM
-- level): when both branches of a conditional are the SAME term, the guard is
-- irrelevant and the `ite` evaluates exactly as that branch — at ANY result type

-- ============================================================================
-- TYPE-SYSTEM EXTENSION: the unit type `Ty.unit`.
--
-- A fourth object-language type whose denotation is the (one-element) `Type`
-- `Unit`. In the Trust verification fragment this is the "no information" /
-- statement-result type: the carrier of side-effecting operations and of the
-- trivial proposition's computational content. Adding it exercises the full
-- type-soundness machinery (Den's `Ty.casesOn`, Tm, and `eval`'s `Tm.rec` all
-- gain a case) at a NON-Nat, NON-Bool denotation, demonstrating the framework
-- is genuinely open to new types and denotations.
--
-- `Unit` is the prelude's reducible abbreviation `Unit : Type := PUnit.{1}`
-- with `Unit.unit : Unit := PUnit.unit.{1}`; `PUnit.{1}` is a real inductive in
-- `Sort 1 = Type` with sole constructor `PUnit.unit.{1}`. So `Unit.unit` is a
-- genuine `Type`-level value and its axiom closure is empty (it unfolds to a
-- constructor application, no axioms).
--
-- REQUIRES the structural edits to `inductive Ty`, `def Den`, `inductive Tm`,
-- and `def eval` described in this PR's notes (a Ty constructor changes the
-- arity of both `Ty.casesOn` and `Tm.rec`).
-- ============================================================================

-- Coherence: the unit TERM `u` evaluates to the unit VALUE `Unit.unit`. This is
-- the canonical (and only) inhabitant law for the new type, holding by `Tm.rec`
-- iota on the `u` minor premise (which is exactly `Unit.unit`) and the
-- `Ty.casesOn` iota that reduces `Den Ty.unit` to `Unit`. No domain axioms.
theorem eval_u : eval Ty.unit Tm.u = Unit.unit := rfl

-- The new type composes with the existing `ite`: an `ite` at result type
-- `Ty.unit` with a `tt` guard takes the `then` branch, just like at every other
-- type (a concrete instance of the general `eval_ite_tt`, now at the unit
-- denotation). Holds by `Tm.rec` iota; no domain axioms.
theorem eval_ite_unit_tt (x y : Tm Ty.unit) :
    eval Ty.unit (Tm.ite Ty.unit Tm.tt x y) = eval Ty.unit x := rfl

-- ... and a `ff` guard takes the `else` branch at the unit type.
theorem eval_ite_unit_ff (x y : Tm Ty.unit) :
    eval Ty.unit (Tm.ite Ty.unit Tm.ff x y) = eval Ty.unit y := rfl

-- Nat LEFT-DISTRIBUTIVITY: `a * (b + c) = a*b + a*c`, by `@Nat.rec` on `c`.
-- `Nat.mul` recurses on its 2nd arg (`mul x 0 = 0`, `mul x (succ y) = add (mul x y) x`)
-- and `Nat.add` on its 2nd arg (`add x 0 = x`, `add x (succ y) = succ (add x y)`).
-- Base `c = 0`: LHS `mul a (add b 0) = mul a b`; RHS `add (mul a b) (mul a 0) =
-- add (mul a b) 0 = mul a b` -- both reduce to `mul a b`, so `rfl`. Step
-- `c = succ k` with `ih : mul a (add b k) = add (mul a b) (mul a k)`: after the
-- definitional reductions the goal is `add (mul a (add b k)) a =
-- add (mul a b) (add (mul a k) a)`; rewrite the LHS by `ih` under
-- `fun z => add z a`, then close by `Nat.add_assoc (mul a b) (mul a k) a`.
theorem nmul_add (a b c : Nat) :
    Nat.mul a (Nat.add b c) = Nat.add (Nat.mul a b) (Nat.mul a c) :=
  @Nat.rec
    (fun k => Nat.mul a (Nat.add b k) = Nat.add (Nat.mul a b) (Nat.mul a k))
    rfl
    (fun k ih =>
      Eq.trans
        (congrArg (fun z => Nat.add z a) ih)
        (Nat.add_assoc (Nat.mul a b) (Nat.mul a k) a))
    c

-- Nat MULTIPLICATION ASSOCIATIVITY: `(a * b) * c = a * (b * c)`, by `@Nat.rec`
-- on `c`. Base `c = 0`: LHS `mul (mul a b) 0 = 0`; RHS `mul a (mul b 0) =
-- mul a 0 = 0` -- both `0`, so `rfl`. Step `c = succ k` with
-- `ih : mul (mul a b) k = mul a (mul b k)`: the goal `motive (succ k)` is, up to
-- iota, `add (mul (mul a b) k) (mul a b) = mul a (add (mul b k) b)` (LHS by the
-- mul-succ reduction with first arg `mul a b`; RHS because `mul b (succ k)`
-- reduces to `add (mul b k) b` under the outer `mul a`). Rewrite the LHS by `ih`
-- under `fun z => add z (mul a b)`, giving `add (mul a (mul b k)) (mul a b)`,
-- then close with `Eq.symm (nmul_add a (mul b k) b)` (left-distributivity, just
-- proven) to fold it back into `mul a (add (mul b k) b)`.
theorem nmul_assoc (a b c : Nat) :
    Nat.mul (Nat.mul a b) c = Nat.mul a (Nat.mul b c) :=
  @Nat.rec
    (fun k => Nat.mul (Nat.mul a b) k = Nat.mul a (Nat.mul b k))
    rfl
    (fun k ih =>
      Eq.trans
        (congrArg (fun z => Nat.add z (Nat.mul a b)) ih)
        (Eq.symm (nmul_add a (Nat.mul b k) b)))
    c

-- TERM-level lift of left-distributivity over TrustCore `nmul`/`nadd`: the
-- program term `nmul x (nadd y z)` evaluates exactly as `nadd (nmul x y) (nmul x z)`.
-- By `Tm.rec` iota both sides reduce to the nested `Nat.mul`/`Nat.add` form
-- `nmul_add` equates. A verified compiler uses this to distribute multiplication
-- over addition on `nat` program terms.
theorem eval_nmul_add (x y z : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul x (Tm.nadd y z))
      = eval Ty.nat (Tm.nadd (Tm.nmul x y) (Tm.nmul x z)) :=
  nmul_add (eval Ty.nat x) (eval Ty.nat y) (eval Ty.nat z)

-- TERM-level lift of multiplication associativity: `nmul (nmul x y) z` evaluates
-- exactly as `nmul x (nmul y z)`. By `Tm.rec` iota both sides reduce to the
-- nested `Nat.mul` form `nmul_assoc` equates. A verified compiler uses this to
-- re-associate multiplication operands on `nat` program terms.
theorem eval_nmul_assoc (x y z : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul (Tm.nmul x y) z) = eval Ty.nat (Tm.nmul x (Tm.nmul y z)) :=
  nmul_assoc (eval Ty.nat x) (eval Ty.nat y) (eval Ty.nat z)

-- TERM-level multiplicative left identity: `nmul (nlit 1) x` evaluates exactly
-- as `x`. By `Tm.rec` iota `eval (nmul (nlit 1) x)` reduces to `Nat.mul 1 (eval x)`
-- (`eval (nlit 1)` reduces to `1`), closed by the already-proven `nmul_one_left`.
theorem eval_nmul_one (x : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul (Tm.nlit 1) x) = eval Ty.nat x :=
  nmul_one_left (eval Ty.nat x)

-- ============================================================================
-- NAT MUL: right-handed identities + RIGHT-DISTRIBUTIVITY, self-proven.
--
-- `Nat.mul m n := Nat.rec 0 (fun _ ih => Nat.add ih m) n` recurses on its 2nd
-- argument, so `mul m 0 ≡ 0` and `mul m (succ k) ≡ Nat.add (mul m k) m` hold
-- DEFINITIONALLY. The two right-handed laws below are therefore `rfl`; the
-- distributivity law is by `@Nat.rec` on the right factor, reusing the already-
-- proven `nmul_comm`/`nmul_one_left` and the confirmed `Nat.add_assoc`/
-- `Nat.add_comm`. (`nmul_zero_left`/`nmul_succ_left`/`nmul_comm`/`nmul_one_left`
-- and the `Nat.add` laws are all in scope above.)
-- ============================================================================

-- Right zero of multiplication: `n * 0 = 0`. DEFINITIONAL — `Nat.mul` recurses
-- on its 2nd arg with base case `Nat.zero`, so `mul n 0` reduces to `0` by iota.
theorem nmul_zero_right (n : Nat) : Nat.mul n 0 = 0 := rfl

-- Right-successor unfolding of multiplication: `n * (succ b) = (n * b) + n`.
-- DEFINITIONAL — the `succ` minor premise of `Nat.mul` is `fun _ ih => add ih n`,
-- so `mul n (succ b)` reduces to `add (mul n b) n` by iota.
theorem nmul_succ_right (a b : Nat) :
    Nat.mul a (Nat.succ b) = Nat.add (Nat.mul a b) a := rfl

-- Right identity of multiplication: `n * 1 = n`. Derived from the already-proven
-- commutativity and left-identity: `mul n 1 = mul 1 n` (`nmul_comm n 1`) and
-- `mul 1 n = n` (`nmul_one_left n`). No induction here; the induction lives in
-- the helpers already in scope.
theorem nmul_one_right (n : Nat) : Nat.mul n 1 = n :=
  Eq.trans (nmul_comm n 1) (nmul_one_left n)

-- Pure additive rearrangement `(p + q) + (a + b) = (p + a) + (q + b)`, the
-- "middle-four interchange" of addition. Used to massage the successor case of
-- right-distributivity. A `Nat.add_assoc`/`Nat.add_comm`/`congrArg` chain (no
-- induction, no domain axioms), in the same equational style as `add_right_comm`
-- and `bvand_assoc` above:
--   (p+q)+(a+b) = p+(q+(a+b))      [Nat.add_assoc p q (a+b)]
--             = p+((q+a)+b)        [congrArg (p+.) (symm (add_assoc q a b))]
--             = p+((a+q)+b)        [congrArg (p+.) (congrArg (.+b) (add_comm q a))]
--             = p+(a+(q+b))        [congrArg (p+.) (add_assoc a q b)]
--             = (p+a)+(q+b)        [symm (add_assoc p a (q+b))].
-- RIGHT-DISTRIBUTIVITY: `(a + b) * c = a*c + b*c`, by `@Nat.rec` on `c`.
-- Base `c = 0`: LHS `mul (add a b) 0 ≡ 0`; RHS `add (mul a 0) (mul b 0) ≡
-- add 0 0 ≡ 0` (both by iota; `add` recurses on 2nd arg), so `rfl`.
-- Step `c = succ j`, `ih : mul (add a b) j = add (mul a j) (mul b j)`:
--   goal LHS  `mul (add a b) (succ j) ≡ add (mul (add a b) j) (add a b)`,
--   goal RHS  ≡ `add (add (mul a j) a) (add (mul b j) b)` (iota on each `mul`).
-- Rewrite LHS by `ih` under `fun z => add z (add a b)` to
--   `add (add (mul a j) (mul b j)) (add a b)`, then close with
--   `add_add_add_comm (mul a j) (mul b j) a b`, whose RHS is defeq to the goal
--   RHS by the `mul (_ ) (succ j)` reductions.
-- TERM-level lifts via `eval` iota. `eval (nlit 0) ≡ 0` / `eval (nlit 1) ≡ 1`
-- and `eval (nmul x y) ≡ Nat.mul (eval x) (eval y)`, so each goal reduces to the
-- helper's statement up to defeq. A verified compiler uses these to collapse
-- `x * 0 -> 0`, `x * 1 -> x`, and to distribute `(x + y) * z -> x*z + y*z` on
-- `nat` program terms.
theorem eval_nmul_zero_right (x : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul x (Tm.nlit 0)) = 0 :=
  nmul_zero_right (eval Ty.nat x)

theorem eval_nmul_one_right (x : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul x (Tm.nlit 1)) = eval Ty.nat x :=
  nmul_one_right (eval Ty.nat x)

-- ============================================================================
-- BITVECTOR LEFT-SHIFT: the modular left-shift operation `bvshl w a k`, modelled
-- as `(a * 2^k) % 2^w` (shift-left-by-k = multiply-by-2^k, then wrap to width
-- `w`). This is exactly the carrier the Trust verifier reasons over for `<<` on a
-- `bv w`. The kernel's REAL `Nat.shiftLeft` is an axiom-FREE Definition
-- (`Nat.shiftLeft m 0 = m`, `Nat.shiftLeft m (succ n) = Nat.mul (Nat.shiftLeft m
-- n) 2`, i.e. `m * 2^n`), so we anchor `bvshl` to it directly. (`Nat.shiftRight`
-- is a prelude AXIOM, so RIGHT shift is deliberately NOT modelled here -- it would
-- break the empty-axiom-closure gate.) No domain axioms.
-- ============================================================================

-- The kernel's `Nat.shiftLeft` unfolds by its own definition: shift-by-zero is
-- the identity (the `Nat.rec` base case is `m` itself), holding by iota+delta.
theorem shl_zero (a : Nat) : Nat.shiftLeft a 0 = a := rfl

-- ...and shift-by-(succ n) doubles the shift-by-n (the `Nat.rec` succ minor
-- premise is `Nat.mul ih 2`). Both reductions are pure iota/delta, no axioms.
theorem shl_succ (a n : Nat) :
    Nat.shiftLeft a (Nat.succ n) = Nat.mul (Nat.shiftLeft a n) 2 := rfl

-- The modular left-shift operation: shift `a` left by `k`, reduced to width `w`.
def bvshl (w a k : Nat) : Nat := (a * 2 ^ k) % (2 ^ w)

-- Metatheorem (the shift-by-zero coherence law): a left shift by `0` is just the
-- width mask. `bvshl w a 0` unfolds to `(a * 2^0) % 2^w`; `2^0` reduces by iota
-- to `1`, so the multiplicand is `Nat.mul a 1`, rewritten to `a` by
-- `nmul_one_right` under the `(. % 2^w)` congruence. Same congrArg shape as the
-- audited `bvadd_comm`; no domain axioms.
theorem bvshl_zero (w a : Nat) : bvshl w a 0 = a % (2 ^ w) :=
  congrArg (fun z => z % (2 ^ w)) (nmul_one_right a)

-- Metatheorem (coherence with the kernel's REAL shift): `bvshl w a 0` agrees with
-- the masked output of the kernel's own `Nat.shiftLeft a 0`. The LHS reduces to
-- `(Nat.mul a 1) % 2^w` (pow iota) and the RHS to `a % 2^w` (`Nat.shiftLeft a 0`
-- iota), so the very same `nmul_one_right` congruence closes the gap -- proving
-- the operation model and the kernel primitive are the same computation at shift
-- amount `0`. No domain axioms.
theorem bvshl_shiftLeft_zero (w a : Nat) :
    bvshl w a 0 = (Nat.shiftLeft a 0) % (2 ^ w) :=
  congrArg (fun z => z % (2 ^ w)) (nmul_one_right a)

-- ============================================================================
-- MORE boolean algebraic laws (XOR identities + distribution), self-proven by
-- single-scrutinee `match` (NO `decide`), and their TrustCore term lifts.
--
-- Verified against the EXACT kernel definitions (clean-kernel/src/env/
-- data_types_nat.rs), each of which recurses on its FIRST argument:
--   Bool.xor a b := Bool.rec (fun _ => Bool) b (Bool.not b) a
--                   (xor false b = b ; xor true b = Bool.not b)
--   Bool.not x   := Bool.rec (fun _ => Bool) true false x
--                   (not false = true ; not true = false)
--   Bool.and a b := Bool.rec (fun _ => Bool) false b a
--                   (and false b = false ; and true b = b)
--   Bool.or  a b := Bool.rec (fun _ => Bool) b true a
--                   (or false b = b ; or true b = true)
-- Every lemma below cases on its HEAD variable alone, so both sides reduce to a
-- common normal form by iota in each branch -- exactly the shape of the
-- already-registered `band_assoc3`/`bor_assoc3`/`absorb_and`/`demorgan_and`.
-- ============================================================================

-- XOR LEFT identities hold DEFINITIONALLY (xor recurses on its first arg):
--   xor false b = b           [iota, false-case = 2nd arg]
--   xor true  b = Bool.not b  [iota, true-case  = Bool.not (2nd arg)]
theorem bxor_false_left (b : Bool) : Bool.xor false b = b := rfl
theorem bxor_true_left (b : Bool) : Bool.xor true b = Bool.not b := rfl

-- XOR RIGHT identities. NOT definitional (xor recurses on the FIRST arg, here a
-- variable), so a `match` on `b` makes each side reduce.
--   b = false : xor false false = false = b ; xor false true = true,
--               and Bool.not false = true (so `bxor_true_right` RHS matches).
--   b = true  : xor true false = Bool.not false = true = b ;
--               xor true true  = Bool.not true (so RHS is `Bool.not true`).
theorem bxor_false_right (b : Bool) : Bool.xor b false = b :=
  match b with | true => rfl | false => rfl

theorem bxor_true_right (b : Bool) : Bool.xor b true = Bool.not b :=
  match b with | true => rfl | false => rfl

-- DISTRIBUTION laws, each by a single case on the head `a` (both connectives
-- reduce by their first argument):
--   AND over OR  : and a (or b c) = or (and a b) (and a c)
--     a=true  : or b c               = or b c                      [rfl]
--     a=false : false                = or false false = false      [rfl]
--   OR over AND  : or a (and b c) = and (or a b) (or a c)
--     a=true  : true                 = and true true = true        [rfl]
--     a=false : and b c              = and b c                     [rfl]
--   AND over XOR : and a (xor b c) = xor (and a b) (and a c)
--     a=true  : xor b c              = xor b c                     [rfl]
--     a=false : false                = xor false false = false     [rfl]
theorem band_distrib_or (a b c : Bool) :
    Bool.and a (Bool.or b c) = Bool.or (Bool.and a b) (Bool.and a c) :=
  match a with | true => rfl | false => rfl

theorem bor_distrib_and (a b c : Bool) :
    Bool.or a (Bool.and b c) = Bool.and (Bool.or a b) (Bool.or a c) :=
  match a with | true => rfl | false => rfl

theorem band_distrib_xor (a b c : Bool) :
    Bool.and a (Bool.xor b c) = Bool.xor (Bool.and a b) (Bool.and a c) :=
  match a with | true => rfl | false => rfl

-- TERM-level lifts via `eval` iota. `eval (bxor a b) = Bool.xor (eval a)(eval b)`,
-- `eval (band ..)`/`eval (bor ..)` reduce to `Bool.and`/`Bool.or`,
-- `eval (bnot b) = Bool.not (eval b)`, `eval ff = false`, `eval tt = true`, so
-- each Bool-level helper's type matches its term goal up to defeq. A verified
-- compiler uses these to rewrite `b ^ false -> b`, `b ^ true -> !b`, and to push
-- AND through OR/XOR (and OR through AND) on program terms.

-- The LEFT identities lift to pure `rfl` (both sides already reduce equal):
--   eval (bxor ff b) = Bool.xor false (eval b) = eval b.
--   eval (bxor tt b) = Bool.xor true  (eval b) = Bool.not (eval b) = eval (bnot b).
theorem eval_bxor_false_left (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bxor Tm.ff b) = eval Ty.bool b := rfl

theorem eval_bxor_true_left (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bxor Tm.tt b) = eval Ty.bool (Tm.bnot b) := rfl

theorem eval_bxor_false_right (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bxor b Tm.ff) = eval Ty.bool b :=
  bxor_false_right (eval Ty.bool b)

theorem eval_bxor_true_right (b : Tm Ty.bool) :
    eval Ty.bool (Tm.bxor b Tm.tt) = eval Ty.bool (Tm.bnot b) :=
  bxor_true_right (eval Ty.bool b)

theorem eval_band_distrib_or (a b c : Tm Ty.bool) :
    eval Ty.bool (Tm.band a (Tm.bor b c))
      = eval Ty.bool (Tm.bor (Tm.band a b) (Tm.band a c)) :=
  band_distrib_or (eval Ty.bool a) (eval Ty.bool b) (eval Ty.bool c)

theorem eval_bor_distrib_and (a b c : Tm Ty.bool) :
    eval Ty.bool (Tm.bor a (Tm.band b c))
      = eval Ty.bool (Tm.band (Tm.bor a b) (Tm.bor a c)) :=
  bor_distrib_and (eval Ty.bool a) (eval Ty.bool b) (eval Ty.bool c)

theorem eval_band_distrib_xor (a b c : Tm Ty.bool) :
    eval Ty.bool (Tm.band a (Tm.bxor b c))
      = eval Ty.bool (Tm.bxor (Tm.band a b) (Tm.band a c)) :=
  band_distrib_xor (eval Ty.bool a) (eval Ty.bool b) (eval Ty.bool c)


-- ============================================================================
-- NAT RIGHT-DISTRIBUTIVITY, derived CLEANLY via COMMUTATIVITY.
--
-- `(a + b) * c = a*c + b*c`. Rather than re-running the `@Nat.rec` induction
-- (the earlier add_add_add_comm/congrArg attempt failed), we REDUCE right-
-- distributivity to the already-proven LEFT-distributivity `nmul_add` using the
-- already-proven `nmul_comm`:
--   mul (a+b) c = mul c (a+b)                [nmul_comm (a+b) c]
--             = add (mul c a) (mul c b)       [nmul_add c a b]
--             = add (mul a c) (mul c b)       [congrArg (. + mul c b) (nmul_comm c a)]
--             = add (mul a c) (mul b c)       [congrArg (mul a c + .) (nmul_comm c b)].
-- Each step is a confirmed empty-axiom-closure helper + `congrArg`/`Eq.trans`,
-- so the whole chain clears the foundational-axiom gate. (`nmul_comm`/`nmul_add`
-- are both in scope above.)
-- ============================================================================
theorem nadd_mul (a b c : Nat) :
    Nat.mul (Nat.add a b) c = Nat.add (Nat.mul a c) (Nat.mul b c) :=
  Eq.trans (nmul_comm (Nat.add a b) c)
    (Eq.trans (nmul_add c a b)
      (Eq.trans (congrArg (fun z => Nat.add z (Nat.mul c b)) (nmul_comm c a))
        (congrArg (fun z => Nat.add (Nat.mul a c) z) (nmul_comm c b))))

-- TERM-level lift of right-distributivity over TrustCore `nadd`/`nmul`: the
-- program term `nmul (nadd x y) z` evaluates exactly as `nadd (nmul x z) (nmul y z)`.
-- By `Tm.rec` iota both sides reduce to the nested `Nat.mul`/`Nat.add` form
-- `nadd_mul` equates. A verified compiler uses this to distribute multiplication
-- over addition on the LEFT factor of `nat` program terms.
theorem eval_nadd_mul (x y z : Tm Ty.nat) :
    eval Ty.nat (Tm.nmul (Tm.nadd x y) z)
      = eval Ty.nat (Tm.nadd (Tm.nmul x z) (Tm.nmul y z)) :=
  nadd_mul (eval Ty.nat x) (eval Ty.nat y) (eval Ty.nat z)

-- ============================================================================
-- POSITIVITY OF Nat.mul AND 2^w, self-proven down to the foundational axioms.
--
-- These underwrite the verifier's modular-carrier reasoning: every modulus
-- `2 ^ w` the bitvector ops reduce by (`bvadd`/`bvsub`/`Bvult`/`bvshl`) is
-- strictly positive, so `% (2 ^ w)` is a real (non-degenerate) remainder.
--
-- Reductions traced against the EXACT kernel defs (clean-kernel/src/env/
-- data_types_nat.rs):
--   Nat.mul m n := Nat.rec 0 (fun _ ih => Nat.add ih m) n   -- recurses on n
--                  (mul m 0 = 0 ; mul m (succ k) = Nat.add (mul m k) m)
--   Nat.add x n := Nat.rec x (fun _ ih => Nat.succ ih) n    -- recurses on n
--                  (add x 0 = x ; add x (succ k) = succ (add x k))
--   Nat.pow m n := Nat.rec 1 (fun _ ih => Nat.mul ih m) n   -- recurses on n
--                  (pow m 0 = 1 ; pow m (succ k) = Nat.mul (pow m k) m)
--   Nat.lt a b  := Nat.le (Nat.succ a) b   (reducible; so `Nat.lt 0 X` is
--                  definitionally `Nat.le 1 X`, since `1 = Nat.succ 0`).
-- All `Nat.le`-family lemmas used below (`Nat.le_refl`, `Nat.le_trans`,
-- `Nat.succ_le_succ`, `Nat.add_le_add_left`, `Nat.zero_le`) are constructive
-- bare-`Nat.le` `Declaration::Theorem`s in the prelude; `Nat.lt_irrefl` and
-- `False.elim` are likewise constructive. No domain axioms.
-- ============================================================================

-- Multiplication preserves strict positivity: `0 < a` and `0 < b` imply
-- `0 < a * b`. By `@Nat.rec` on `b` with the hypothesis-carrying motive
-- `fun k => Nat.lt 0 k -> Nat.lt 0 (Nat.mul a k)` (so the `b = 0` branch has the
-- contradictory `0 < 0` to discharge). `ha : Nat.lt 0 a` is fixed outside.
--   Base `b = 0`: from `h0 : Nat.lt 0 0` (i.e. `Nat.le 1 0`), `Nat.lt_irrefl 0 h0`
--     is `False`, closed by `@False.elim` at the goal `Nat.lt 0 (Nat.mul a 0)`.
--   Step `b = succ j`: goal `Nat.lt 0 (Nat.mul a (succ j))`; `Nat.mul a (succ j)`
--     reduces to `Nat.add (Nat.mul a j) a`, so the goal is `Nat.le 1 ((a*j) + a)`.
--     Chain `1 <= succ (a*j) <= (a*j) + a` by `Nat.le_trans`:
--       lower `Nat.succ_le_succ 0 (a*j) (Nat.zero_le (a*j)) : Nat.le 1 (succ (a*j))`;
--       upper `Nat.add_le_add_left 1 a ha (a*j) : Nat.le ((a*j)+1) ((a*j)+a)`, and
--       `(a*j) + 1 = (a*j) + succ 0 = succ ((a*j) + 0) = succ (a*j)` definitionally,
--       so its type is `Nat.le (succ (a*j)) ((a*j)+a)`. The `ih` is not needed.
theorem nmul_pos (a b : Nat) : Nat.lt 0 a -> Nat.lt 0 b -> Nat.lt 0 (Nat.mul a b) :=
  fun ha hb =>
    @Nat.rec
      (fun k => Nat.lt 0 k -> Nat.lt 0 (Nat.mul a k))
      (fun h0 => @False.elim (Nat.lt 0 (Nat.mul a 0)) (Nat.lt_irrefl 0 h0))
      (fun j _ih _hsj =>
        @Nat.le_trans 1 (Nat.succ (Nat.mul a j)) (Nat.add (Nat.mul a j) a)
          (@Nat.succ_le_succ 0 (Nat.mul a j) (Nat.zero_le (Nat.mul a j)))
          (Nat.add_le_add_left 1 a ha (Nat.mul a j)))
      b hb

-- Strict positivity of the width modulus: `0 < 2 ^ w` at every width `w`. This
-- is the fact that makes `% (2 ^ w)` a genuine remainder for `bvadd`/`bvsub`/
-- `Bvult`/`bvshl`. By `@Nat.rec` on `w`:
--   Base `w = 0`: `2 ^ 0` reduces (pow iota) to `1`, so the goal `Nat.lt 0 (2^0)`
--     is `Nat.le 1 1`, witnessed by `Nat.le_refl 1`.
--   Step `w = succ k`: `2 ^ (succ k)` reduces (pow iota) to `Nat.mul (2 ^ k) 2`,
--     and `nmul_pos (2 ^ k) 2 ih (..)` gives `Nat.lt 0 (Nat.mul (2 ^ k) 2)`,
--     where `ih : Nat.lt 0 (2 ^ k)` and the `0 < 2` witness is
--     `Nat.succ_le_succ 0 1 (Nat.zero_le 1) : Nat.le 1 2` (defeq `Nat.lt 0 2`).
theorem two_pow_pos (w : Nat) : Nat.lt 0 (2 ^ w) :=
  @Nat.rec
    (fun k => Nat.lt 0 (2 ^ k))
    (Nat.le_refl 1)
    (fun k ih => nmul_pos (2 ^ k) 2 ih (@Nat.succ_le_succ 0 1 (Nat.zero_le 1)))
    w

-- ============================================================================
-- BITVECTOR LEFT-SHIFT, shift-by-ONE laws + doubling coherence. Building on
-- `bvshl`/`shl_zero`/`shl_succ` and the kernel's `Nat.shiftLeft`/`Nat.mul`/
-- `Nat.pow`/`Nat.add`, all axiom-free. A left shift by 1 is multiplication by 2,
-- which (modularly) is self-addition -- the carrier law a verified compiler uses
-- to rewrite `x << 1 -> x + x`. Traced against the EXACT kernel definitions:
--   Nat.shiftLeft m n := Nat.rec m (fun _ ih => Nat.mul ih 2) n
--                        (shiftLeft m 0 = m ; shiftLeft m (succ n) = mul (shiftLeft m n) 2)
--   Nat.pow m n       := Nat.rec 1 (fun _ ih => Nat.mul ih m) n
--                        (pow m 0 = 1 ; pow m (succ n) = mul (pow m n) m)
--   Nat.mul x n       := Nat.rec 0 (fun _ ih => Nat.add ih x) n
--                        (mul x 0 = 0 ; mul x (succ y) = add (mul x y) x)
--   Nat.add x n       recurses on 2nd arg (add x 0 = x ; add x (succ y) = succ (add x y))
-- No `decide`, no `Nat.mod` unfolding (it is Opaque and stays stuck under the
-- shared `% 2^w` mask), no domain axioms. (`Nat.shiftRight` is a prelude AXIOM
-- and is deliberately untouched.)
-- ============================================================================

-- Shift-by-one is doubling: `Nat.shiftLeft a 1 = Nat.mul a 2`. The literal `1`
-- expands to `Nat.succ Nat.zero`, so `shl_succ a 0` gives
-- `shiftLeft a (succ 0) = Nat.mul (shiftLeft a 0) 2`; `shl_zero a` rewrites the
-- inner `shiftLeft a 0` to `a` under `fun z => Nat.mul z 2`. Pure
-- `Eq.trans`/`congrArg` over the two in-scope shift helpers; no domain axioms.
theorem shl_one (a : Nat) : Nat.shiftLeft a 1 = Nat.mul a 2 :=
  Eq.trans (shl_succ a 0) (congrArg (fun z => Nat.mul z 2) (shl_zero a))

-- Modular shift-by-one over the carrier: `bvshl w a 1 = (Nat.mul a 2) % 2^w`.
-- `bvshl w a 1` unfolds (delta) to `(a * 2^1) % 2^w`; `2^1 = pow 2 (succ 0)`
-- reduces by iota to `Nat.mul (pow 2 0) 2 = Nat.mul 1 2`, a GROUND term that
-- structurally reduces to `2`. So `a * 2^1` is defeq to `Nat.mul a 2` and the
-- whole equation holds by `rfl`. (Unlike `bvshl_zero`, no `nmul_one_right` is
-- needed: the RHS keeps the `Nat.mul a 2` form rather than collapsing it to `a`.)
theorem bvshl_one (w a : Nat) : bvshl w a 1 = (Nat.mul a 2) % (2 ^ w) := rfl

-- `Nat.mul a 2 = Nat.add a a`. `mul a 2 = mul a (succ (succ 0))` reduces by iota
-- to `add (add (mul a 0) a) a = add (add 0 a) a`; the goal RHS is `add a a`, so
-- `congrArg (fun z => Nat.add z a) (Nat.zero_add a)` (with
-- `Nat.zero_add a : Nat.add 0 a = a`) closes the residual `add (add 0 a) a =
-- add a a`. The goal LHS `Nat.mul a 2` is defeq to that proof's LHS by the iota
-- trace. Confirmed-constructive `Nat.zero_add` + `congrArg`; no domain axioms.
theorem two_mul (a : Nat) : Nat.mul a 2 = Nat.add a a :=
  congrArg (fun z => Nat.add z a) (Nat.zero_add a)

-- Doubling coherence on the carrier: a modular shift-by-one equals modular
-- self-addition -- `bvshl w a 1 = bvadd w a a`. The LHS is defeq to
-- `(Nat.mul a 2) % 2^w` (by `2^1 ≡ 2`, as in `bvshl_one`) and the RHS unfolds to
-- `(a + a) % 2^w = (Nat.add a a) % 2^w`, so `congrArg (fun z => z % 2^w) (two_mul a)`
-- bridges them under the shared mask. Exact congrArg shape of the audited
-- `bvadd_comm`; no domain axioms. (`bvshl` has no `Tm` constructor, so this stays
-- at the operation level -- there is no term-level `eval` lift to add.)
theorem bvshl_eq_bvadd_self (w a : Nat) : bvshl w a 1 = bvadd w a a :=
  congrArg (fun z => z % (2 ^ w)) (two_mul a)

-- ============================================================================
-- NAT ORDER theory (Prop-level): additive monotonicity of `Nat.le`, plus the
-- `Bvult` order facts that build on it. Term-level `nle` TRUTH is blocked
-- (`eval (nle x y) = decide (Nat.le ..)` and `decide` does NOT reduce), so the
-- facts live at the `Nat` / `Bvult` level -- exactly the layer the verifier's
-- chained-comparison reasoning consumes.
--
-- Verified against the EXACT prelude signatures (clean-kernel order_arith.rs /
-- nat_arith_order_proof.rs -- all CONSTRUCTIVE `Declaration::Theorem`s with
-- empty axiom closure, #3604; the legacy `Declaration::Axiom` forms are guarded
-- no-ops once the Theorem form is present):
--   Nat.add_le_add_left  : forall a b, Nat.le a b -> forall c, Nat.le (Nat.add c a) (Nat.add c b)
--   Nat.add_le_add_right : forall a b, Nat.le a b -> forall c, Nat.le (Nat.add a c) (Nat.add b c)
--   Nat.le_trans         : forall a b c, Nat.le a b -> Nat.le b c -> Nat.le a c
--   Nat.le_of_lt         : forall {a b}, Nat.lt a b -> Nat.le a b  (a,b IMPLICIT)
--   Nat.lt_of_le_of_lt   : forall a b c, Nat.le a b -> Nat.lt b c -> Nat.lt a c
-- (`Nat.le_of_lt` / `Nat.lt_of_le_of_lt` arg forms are exactly those already
-- used by the in-scope `bvult_trans`.)
-- ============================================================================

-- Thin TrustCore handles for the two one-sided monotonicity prelude lemmas:
-- adding the SAME `c` to both sides of `a <= b` preserves the order, on the
-- LEFT (`c + a <= c + b`) and on the RIGHT (`a + c <= b + c`). Direct
-- applications of the constructive `Nat.add_le_add_left` / `Nat.add_le_add_right`
-- (args `a b h c`); no axioms beyond those (empty) closures.
theorem nadd_le_mono_left (a b c : Nat) :
    Nat.le a b -> Nat.le (Nat.add c a) (Nat.add c b) :=
  fun h => Nat.add_le_add_left a b h c

theorem nadd_le_mono_right (a b c : Nat) :
    Nat.le a b -> Nat.le (Nat.add a c) (Nat.add b c) :=
  fun h => Nat.add_le_add_right a b h c

-- Two-sided additive monotonicity of `Nat.le`: `a <= b` and `c <= d` give
-- `a + c <= b + d`. Proven compositionally (the same proof term the kernel's own
-- `Nat.add_le_add` uses): bump the LEFT endpoint by `c` with `add_le_add_right`
-- (`a + c <= b + c`), bump the RIGHT endpoint by `b` with `add_le_add_left`
-- (`b + c <= b + d`), and chain with `Nat.le_trans` at the witnesses
-- `(a + c)`, `(b + c)`, `(b + d)`. No domain axioms.
theorem nadd_le_mono (a b c d : Nat) :
    Nat.le a b -> Nat.le c d -> Nat.le (Nat.add a c) (Nat.add b d) :=
  fun h1 h2 =>
    @Nat.le_trans (Nat.add a c) (Nat.add b c) (Nat.add b d)
      (Nat.add_le_add_right a b h1 c)
      (Nat.add_le_add_left c d h2 b)

-- Bvult-to-le: an unsigned strict `<u` over the carrier entails the non-strict
-- `<=` of the masked values. `Bvult w a b` is the `def` `Nat.lt (a % 2^w)
-- (b % 2^w)`, so `h` is accepted as that `Nat.lt` by delta, and `Nat.le_of_lt h`
-- is the non-strict witness — `a`/`b` are IMPLICIT and inferred from `h`'s type.
-- (Same arg form as the `Nat.le_of_lt` call inside the in-scope `bvult_trans`.)
-- No axioms.
theorem Bvult_le (w a b : Nat) :
    Bvult w a b -> Nat.le (a % (2 ^ w)) (b % (2 ^ w)) :=
  fun h => Nat.le_of_lt h

-- Mixed le/strict transitivity at the bv level (companion to the in-scope
-- strict/strict `bvult_trans`): a non-strict `<=` of the masked values followed
-- by a `<u` yields a `<u`. The goal `Bvult w a c` is the `def`
-- `Nat.lt (a % 2^w) (c % 2^w)`, closed by `Nat.lt_of_le_of_lt` at the masked
-- witnesses (exactly the spine `bvult_trans` uses). No domain axioms.
theorem Bvult_lt_of_le_left (w a b c : Nat) :
    Nat.le (a % (2 ^ w)) (b % (2 ^ w)) -> Bvult w b c -> Bvult w a c :=
  fun hle h =>
    Nat.lt_of_le_of_lt (a % (2 ^ w)) (b % (2 ^ w)) (c % (2 ^ w)) hle h


-- ============================================================================
-- MODULAR MULTIPLICATION: the width-`w` modular multiply `bvmul w a b`, the
-- carrier the Trust verifier reasons over for `*` on a `bv w` (value reduced
-- `% 2 ^ w`, matching clean's BitVec `Fin (2 ^ w)` representation). Mirrors the
-- audited `bvadd`/`bvadd_comm` shape exactly, but over `Nat.mul`. Commutativity
-- is `congrArg (. % 2^w)` on the already-proven, self-induced `nmul_comm`
-- (the prelude has NO mul lemmas, so `nmul_comm` is the in-scope self-proof).
-- `bvmul` is written with the EXPLICIT kernel `Nat.mul a b` (not surface `*`) so
-- the `congrArg` motive `fun z => z % (2 ^ w)` lands on EXACTLY the `nmul_comm`
-- LHS/RHS by delta, with no reliance on `*`-typeclass resolution inside the
-- proof term. No domain axioms. (The `def bvmul` itself is placed up beside the
-- other `bv*` op defs — see the STRUCTURAL EDITS in notes — because `eval`'s new
-- `Tm.rec` minor references it; the THREE theorems below paste here, before
-- `end TrustCore`.)
-- ============================================================================

-- Metatheorem: bitvector multiplication is commutative at every width — the
-- modular-`bvmul` analogue of the audited `bvadd_comm`. Proven by congruence of
-- the `(. % 2^w)` mask over the self-proven `nmul_comm`; no domain axioms.
theorem bvmul_comm (w a b : Nat) : bvmul w a b = bvmul w b a :=
  congrArg (fun z => z % (2 ^ w)) (nmul_comm a b)

-- Coherence: the term-level `mul`/`bvmul` are the same computation — `eval` of a
-- `Tm.mul` term is exactly `bvmul` applied to the operands' values, so the
-- intrinsic term semantics agrees with the standalone modular-multiply operation
-- the verifier reasons about. Holds by `Tm.rec` iota (mirrors `eval_add`).
theorem eval_mul (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.mul w x y) = bvmul w (eval (Ty.bv w) x) (eval (Ty.bv w) y) := rfl

-- TERM-level commutativity of TrustCore `mul`: the program term `mul x y`
-- evaluates exactly as `mul y x`. By `Tm.rec` iota both sides reduce to the
-- `bvmul w (eval x) (eval y)` / `bvmul w (eval y) (eval x)` form that
-- `bvmul_comm` equates. A verified compiler uses this to commute multiplication
-- operands on `bv w` program terms (mirrors `eval_add_comm`).
theorem eval_mul_comm (w : Nat) (x y : Tm (Ty.bv w)) :
    eval (Ty.bv w) (Tm.mul w x y) = eval (Ty.bv w) (Tm.mul w y x) :=
  bvmul_comm w (eval (Ty.bv w) x) (eval (Ty.bv w) y)

-- ============================================================================
-- BITVECTOR right-zero / right-identity CONSTANT laws over the carrier, proven
-- by BIT EXTENSIONALITY (`Nat.eq_of_testBit_eq`) + the registered per-gate
-- testBit-adequacy lemmas + the in-scope Bool right-zero/right-unit helpers.
--
-- These are the carrier-level (raw `Nat 0`) facts a bit-blaster uses to fold
-- `x &&& 0 -> 0`, `x ||| 0 -> x`, `x ^^^ 0 -> x`. Each is proven bit-by-bit:
-- bit `i` of `0` is `false` (`Nat.testBit_zero_eq_false`), and the boolean
-- connective collapses on a `false` operand (`band_false`/`bor_false`/
-- `bxor_false_right`, all already in scope and audited).
--
-- NOTE on the absent TERM-level lifts: `Tm.lit w 0` evaluates (Tm.rec iota) to
-- `0 % 2 ^ w`, NOT to `0`. `Nat.mod` is opaque/well-founded with NO constructive
-- `Nat.zero_mod` lemma in the prelude, so `0 % 2 ^ w` does NOT reduce to `0` and
-- a term-level `eval (land w x (lit w 0)) = ...` statement cannot clear the
-- empty-axiom-closure gate. The term-level lits-zero theorems are therefore
-- DELIBERATELY OMITTED; only the carrier-level laws (about the raw `Nat 0`) are
-- delivered here.
--
-- Traced against the EXACT registered signatures:
--   Nat.eq_of_testBit_eq      : (m n : Nat) -> ((i:Nat) -> testBit m i = testBit n i) -> m = n
--   Nat.testBit_and (m n i)   : testBit (Nat.land m n) i = (testBit m i && testBit n i)
--   Nat.testBit_or  (m n i)   : testBit (Nat.lor  m n) i = (testBit m i || testBit n i)
--   Nat.testBit_xor (m n i)   : testBit (Nat.xor  m n) i = Bool.xor (testBit m i) (testBit n i)
--   Nat.testBit_zero_eq_false : (i : Nat) -> testBit 0 i = false
-- and the in-scope helpers band_false / bor_false / bxor_false_right. No domain
-- axioms.
-- ============================================================================

-- `bvand a 0 = 0`. `bvand a 0` is delta `Nat.land a 0`. For bit `i`:
--   testBit (land a 0) i = (testBit a i && testBit 0 i)   [testBit_and]
--                        = (testBit a i && false)         [congrArg, testBit_zero_eq_false]
--                        = false                          [band_false]
--                        = testBit 0 i                    [symm testBit_zero_eq_false].
theorem bvand_zero (a : Nat) : bvand a 0 = 0 :=
  Nat.eq_of_testBit_eq (Nat.land a 0) 0
    (fun i =>
      Eq.trans (Nat.testBit_and a 0 i)
        (Eq.trans
          (congrArg (fun z => Bool.and (Nat.testBit a i) z) (Nat.testBit_zero_eq_false i))
          (Eq.trans (band_false (Nat.testBit a i))
            (Eq.symm (Nat.testBit_zero_eq_false i)))))

-- `bvor a 0 = a`. `bvor a 0` is delta `Nat.lor a 0`. For bit `i`:
--   testBit (lor a 0) i = (testBit a i || testBit 0 i)    [testBit_or]
--                       = (testBit a i || false)          [congrArg, testBit_zero_eq_false]
--                       = testBit a i                     [bor_false].
theorem bvor_zero (a : Nat) : bvor a 0 = a :=
  Nat.eq_of_testBit_eq (Nat.lor a 0) a
    (fun i =>
      Eq.trans (Nat.testBit_or a 0 i)
        (Eq.trans
          (congrArg (fun z => Bool.or (Nat.testBit a i) z) (Nat.testBit_zero_eq_false i))
          (bor_false (Nat.testBit a i))))

-- `bvxor a 0 = a`. `bvxor a 0` is delta `Nat.xor a 0`. For bit `i`:
--   testBit (xor a 0) i = Bool.xor (testBit a i) (testBit 0 i)  [testBit_xor]
--                       = Bool.xor (testBit a i) false          [congrArg, testBit_zero_eq_false]
--                       = testBit a i                           [bxor_false_right].
theorem bvxor_zero (a : Nat) : bvxor a 0 = a :=
  Nat.eq_of_testBit_eq (Nat.xor a 0) a
    (fun i =>
      Eq.trans (Nat.testBit_xor a 0 i)
        (Eq.trans
          (congrArg (fun z => Bool.xor (Nat.testBit a i) z) (Nat.testBit_zero_eq_false i))
          (bxor_false_right (Nat.testBit a i))))

-- ============================================================================
-- NAT TRUNCATED SUBTRACTION (`Nat.sub`) theory, self-proven, + the `nsub` TERM.
--
-- Traced against the EXACT kernel definitions
-- (clean-kernel/src/env/data_types_nat.rs), both axiom-free reducible defs:
--   Nat.pred n := Nat.rec Nat.zero (fun m _ => m) n   -- recurses on its arg
--                 (pred 0 = 0 ; pred (succ m) = m)
--   Nat.sub m n := Nat.rec m (fun _ ih => Nat.pred ih) n   -- recurses on 2nd arg
--                 (sub m 0 = m ; sub m (succ n) = Nat.pred (sub m n))
-- So the two unfolding laws below hold DEFINITIONALLY (by iota), and the
-- left-zero law `sub 0 n = 0` is a one-line `@Nat.rec` on `n` (each successor
-- step rewrites `pred (sub 0 k)` to `pred 0`, which is `0` by pred's base-case
-- iota). No `decide`, no `Nat.mod`, no domain axioms.
-- ============================================================================

-- Right-zero of truncated subtraction: `sub n 0 = n`. DEFINITIONAL — `Nat.sub`
-- recurses on its 2nd arg with base case `m` itself, so `sub n 0` reduces to `n`
-- by iota.
theorem nsub_zero (n : Nat) : Nat.sub n 0 = n := rfl

-- Successor unfolding of subtraction: `sub n (succ m) = pred (sub n m)`.
-- DEFINITIONAL — the `succ` minor premise of `Nat.sub` is `fun _ ih => pred ih`,
-- so `sub n (succ m)` reduces to `Nat.pred (sub n m)` by iota.
theorem nsub_succ (n m : Nat) :
    Nat.sub n (Nat.succ m) = Nat.pred (Nat.sub n m) := rfl

-- Left-zero of truncated subtraction: `sub 0 n = 0` at every `n`, by `@Nat.rec`
-- on `n`. Base `n = 0`: `sub 0 0 = 0` by iota, `rfl`. Step `n = succ k` with
-- `ih : sub 0 k = 0`: the goal `sub 0 (succ k) = 0` is, after the `Nat.sub`
-- succ-iota, `pred (sub 0 k) = 0`; `congrArg Nat.pred ih : pred (sub 0 k) =
-- pred 0`, and `pred 0` reduces to `0` by the base-case iota of `Nat.pred`, so
-- its type is defeq to the goal. No domain axioms.
theorem zero_nsub (n : Nat) : Nat.sub 0 n = 0 :=
  @Nat.rec
    (fun k => Nat.sub 0 k = 0)
    rfl
    (fun k ih => congrArg (fun z => Nat.pred z) ih)
    n

-- Coherence: the TrustCore subtraction TERM `nsub` evaluates to the underlying
-- `Nat.sub` of its operands' values (by `Tm.rec` iota), mirroring `eval_nadd`/
-- `eval_nmul`. So the term layer and the `Nat.sub` op layer are the same
-- computation. Requires the structural `Tm`/`eval` edits in this PR's notes.
theorem eval_nsub (x y : Tm Ty.nat) :
    eval Ty.nat (Tm.nsub x y) = Nat.sub (eval Ty.nat x) (eval Ty.nat y) := rfl

-- TERM-level right-zero of subtraction: `nsub x (nlit 0)` evaluates exactly as
-- `x`. `eval (nlit 0)` reduces to `0`, so `eval (nsub x (nlit 0))` reduces
-- (Tm.rec iota) to `Nat.sub (eval x) 0`, closed by the already-proven
-- `nsub_zero`. A verified compiler uses this to collapse `x - 0 -> x` on `nat`
-- program terms.
theorem eval_nsub_zero (x : Tm Ty.nat) :
    eval Ty.nat (Tm.nsub x (Tm.nlit 0)) = eval Ty.nat x :=
  nsub_zero (eval Ty.nat x)


-- ============================================================================
-- PRODUCT TYPE `Ty.prod` (composite type — Rust tuples). The FIRST type whose
-- denotation is RECURSIVE: `Den (Ty.prod a b) = Prod (Den a) (Den b)`. This is
-- why `Den` is now defined by `@Ty.rec` (the recursive eliminator) rather than
-- `@Ty.casesOn`: the `prod` minor receives the recursive IH results `Da Db`
-- (the motive — i.e. `Den` — applied to the two component types) and forms the
-- prelude pair `Prod Da Db`. `@Ty.rec`'s iota rule for the `prod` constructor
-- substitutes those IHs, so `Den (Ty.prod a b)` reduces to `Prod (Den a)(Den b)`
-- by construction (the same recursive-recursor iota the existing `eval` relies
-- on via `@Tm.rec`; the non-recursive minors `bool/bv/nat/unit` reduce exactly
-- as before, so every earlier theorem is unaffected). The intrinsically-typed
-- `pair`/`fst`/`snd` TERMS give tuple construction and projection; their
-- evaluator cases use the prelude `Prod.mk`/`Prod.fst`/`Prod.snd` (the latter two
-- reducible projections), so the β-η laws below hold by `Tm.rec` iota followed by
-- `Prod` projection reduction. No domain axioms.
--
-- REQUIRES the structural edits to `inductive Ty`, `def Den` (now `@Ty.rec`),
-- `inductive Tm`, and `def eval` described in this PR's notes.
-- ============================================================================

-- The first projection of a constructed pair is its left component: evaluating
-- `fst (pair x y)` is exactly evaluating `x`, at ANY component types. By `Tm.rec`
-- iota the `fst` case reduces to `Prod.fst (Prod.mk (eval x) (eval y))`, and the
-- prelude `Prod.fst`/`Prod.mk` projection reduction collapses it to `eval x`.
theorem eval_fst_pair (a b : Ty) (x : Tm a) (y : Tm b) :
    eval a (Tm.fst a b (Tm.pair a b x y)) = eval a x := rfl

-- The second projection of a constructed pair is its right component (the dual
-- law), by the same `Tm.rec` iota + `Prod.snd`/`Prod.mk` projection reduction.
theorem eval_snd_pair (a b : Ty) (x : Tm a) (y : Tm b) :
    eval b (Tm.snd a b (Tm.pair a b x y)) = eval b y := rfl

-- ============================================================================
-- SUM / COPRODUCT TYPE `Ty.sum` (composite type — Rust enums / `Either`). The
-- SECOND recursive-denotation type after `Ty.prod`: `Den (Ty.sum a b) =
-- Sum (Den a) (Den b)`. As with `prod`, `Den`'s `@Ty.rec` gains a `sum` minor
-- `(fun _a _b Da Db => Sum Da Db)` that receives the recursive IH results
-- `Da Db` (the motive — i.e. `Den` — applied to the two component types) and
-- forms the prelude disjoint union `Sum Da Db`. `@Ty.rec`'s iota for the `sum`
-- constructor substitutes those IHs, so `Den (Ty.sum a b)` reduces to
-- `Sum (Den a)(Den b)` by construction (the non-recursive minors and `prod`
-- reduce exactly as before, so every earlier theorem is unaffected).
--
-- The prelude `Sum` (clean-kernel/src/env/data_types.rs, registered by
-- `with_prelude` via `init_sum`, right beside `init_prod`) has EXACTLY the
-- `Prod` universe profile — `Sum : Type u -> Type v -> Type (max u v)`,
-- `Sum.inl : {a : Type u} -> {b : Type v} -> a -> Sum a b`, `Sum.inr` dual —
-- so `Sum (Den a)(Den b) : Type 0`, compatible with `Den : Ty -> Type`. The
-- `@Sum.inl (Den a)(Den b) ihx` form (all-explicit, filling the implicit
-- `a := Den a`, `b := Den b`) mirrors the audited `@Prod.mk (Den a)(Den b) ..`.
--
-- The intrinsically-typed `inl`/`inr` TERMS give the two coproduct injections.
-- A faithful case eliminator `scase s f g` is NOT expressible: it needs `f`,`g`
-- to be FUNCTIONS `Tm a -> Tm c` / `Tm b -> Tm c`, but TrustCore `Tm` has no
-- function terms — so case analysis is DELIBERATELY OMITTED. Only the injection
-- coherence laws are delivered; each holds by `Tm.rec` iota (the `inl`/`inr`
-- minor is exactly `@Sum.inl`/`@Sum.inr` of the evaluated subterm). No domain
-- axioms (the `Sum` constructors are pure constructor applications).
--
-- REQUIRES the structural edits to `inductive Ty`, `def Den`, `inductive Tm`,
-- and `def eval` described in this PR's notes.
-- ============================================================================

-- The left injection TERM `inl` evaluates to the prelude left injection of its
-- evaluated subterm: `eval (inl x)` is exactly `Sum.inl (eval x)`, at ANY
-- component types. By `Tm.rec` iota the `inl` minor reduces to
-- `@Sum.inl (Den a)(Den b) (eval a x)`, and the new `Den` sum-minor iota gives
-- the result type `Sum (Den a)(Den b)`. Mirrors `eval_fst_pair`'s rfl shape.
theorem eval_inl (a b : Ty) (x : Tm a) :
    eval (Ty.sum a b) (Tm.inl a b x) = @Sum.inl (Den a) (Den b) (eval a x) := rfl

-- The right injection TERM `inr` evaluates to the prelude right injection of its
-- evaluated subterm (the dual law), by the same `Tm.rec` iota on the `inr`
-- minor `@Sum.inr (Den a)(Den b) (eval b y)`.
theorem eval_inr (a b : Ty) (y : Tm b) :
    eval (Ty.sum a b) (Tm.inr a b y) = @Sum.inr (Den a) (Den b) (eval b y) := rfl

-- ============================================================================
-- OPTION TYPE `Ty.opt` (composite type — Rust `Option<T>`). The SECOND type
-- with a RECURSIVE denotation, and the FIRST UNARY-recursive one:
-- `Den (Ty.opt a) = Option (Den a)`. Mirrors the `Ty.prod` recipe exactly, but
-- the constructor takes a SINGLE `Ty` field, so its `@Ty.rec` minor receives
-- exactly one recursive IH result `Da` (= `Den a`) and forms the prelude
-- `Option Da`. The kernel prelude provides `Option : {α : Sort u} → Sort u`
-- with constructors `Option.none : {α} → Option α` and
-- `Option.some : {α} → α → Option α` (confirmed in
-- clean-kernel/src/env/data_types.rs: `α` is IMPLICIT, the `some` value is
-- explicit). The intrinsically-typed `some`/`none` TERMS give optional
-- construction; their evaluator cases use `@Option.some (Den a)`/
-- `@Option.none (Den a)` (the `@` makes the implicit `α` explicit, exactly as
-- the `prod` minors do for `Prod.mk`). The β-laws below hold by `Tm.rec` iota
-- followed by the constructor's own reduction. `Option.some`/`Option.none` are
-- inductive constructors (no axioms) and `Den`/`eval`/`Ty.rec`/`Tm.rec` are all
-- axiom-free, so both theorems clear the empty-axiom-closure gate. No domain
-- axioms.
--
-- REQUIRES the structural edits to `inductive Ty`, `def Den` (now `@Ty.rec`),
-- `inductive Tm`, and `def eval` described in this PR's notes.
-- ============================================================================

-- Coherence: the optional-construction TERM `some` evaluates to the prelude
-- `Option.some` of its payload's value, at ANY component type. By `Tm.rec` iota
-- the `some` minor reduces to `@Option.some (Den a) (eval a x)`.
theorem eval_some (a : Ty) (x : Tm a) :
    eval (Ty.opt a) (Tm.some a x) = @Option.some (Den a) (eval a x) := rfl

-- Coherence (the dual / nullary law): the `none` TERM evaluates to the prelude
-- `Option.none` at the denoted payload type. By `Tm.rec` iota the `none` minor
-- (which takes no subterm) reduces to `@Option.none (Den a)`.
theorem eval_none (a : Ty) :
    eval (Ty.opt a) (Tm.none a) = @Option.none (Den a) := rfl

-- ============================================================================
-- MORE PRODUCT laws — constructed-pair coherence, the DERIVED swap term, and
-- NESTED projection beta. No new `Ty`/`Tm` constructors and NO structural edits:
-- every law below is about CONSTRUCTED pairs built from the shipped
-- `Tm.pair`/`Tm.fst`/`Tm.snd`, so each holds by `Tm.rec` iota followed by the
-- prelude `Prod.fst`/`Prod.snd`-on-`Prod.mk` projection reduction (the SAME two
-- reductions already audited by `eval_fst_pair`/`eval_snd_pair`). Hence `:= rfl`
-- and an empty axiom closure. `pair`/`fst`/`snd` eval minors are
--   pair: (fun a b _x _y ihx ihy => @Prod.mk (Den a)(Den b) ihx ihy)
--   fst : (fun a b _p ihp => @Prod.fst (Den a)(Den b) ihp)
--   snd : (fun a b _p ihp => @Prod.snd (Den a)(Den b) ihp)
-- so `eval (Tm.fst .. (Tm.pair .. x y))` reduces to `Prod.fst (Prod.mk (eval x)(eval y))`
-- = `eval x` by projection iota, and dually for `snd`. (Prod-eta — a law about an
-- ARBITRARY `p` rather than a constructed pair — is deliberately NOT attempted: it
-- needs structure-eta, which is not among the confirmed-constructive reductions.)
-- ============================================================================

-- Constructor coherence (the `pair` analogue of `eval_add`/`eval_mul`): evaluating
-- a constructed pair is exactly the prelude `Prod.mk` of the components' values.
-- By `Tm.rec` iota on the `pair` minor. No domain axioms.
theorem eval_pair (a b : Ty) (x : Tm a) (y : Tm b) :
    eval (Ty.prod a b) (Tm.pair a b x y)
      = @Prod.mk (Den a) (Den b) (eval a x) (eval b y) := rfl

-- DERIVED swap term on a CONSTRUCTED pair: `pair b a (snd (pair x y)) (fst (pair x y))`
-- is the order-swapped tuple. Its evaluation is the prelude `Prod.mk` with the
-- components transposed — `(eval b y, eval a x)`. The inner `snd`/`fst` of the
-- constructed `(x,y)` beta-reduce (projection on `Prod.mk`) to `eval b y` / `eval a x`,
-- then the outer `pair b a` minor forms `@Prod.mk (Den b)(Den a)`. Holds by `Tm.rec`
-- iota + `Prod` projection reduction; no constructor added, no domain axioms.
theorem eval_swap_pair (a b : Ty) (x : Tm a) (y : Tm b) :
    eval (Ty.prod b a)
        (Tm.pair b a (Tm.snd a b (Tm.pair a b x y)) (Tm.fst a b (Tm.pair a b x y)))
      = @Prod.mk (Den b) (Den a) (eval b y) (eval a x) := rfl

-- Swap roundtrip projections: the FIRST projection of the swapped pair recovers the
-- ORIGINAL right component, and the SECOND recovers the original left component —
-- the defining property of swap, at the term level. Each is two projection-beta
-- reductions deep (inner `snd`/`fst` on `(x,y)`, then outer `fst`/`snd` on the
-- swapped `Prod.mk`), all by `Tm.rec` iota + `Prod` projection. No domain axioms.
theorem eval_swap_pair_fst (a b : Ty) (x : Tm a) (y : Tm b) :
    eval b
        (Tm.fst b a
          (Tm.pair b a (Tm.snd a b (Tm.pair a b x y)) (Tm.fst a b (Tm.pair a b x y))))
      = eval b y := rfl

theorem eval_swap_pair_snd (a b : Ty) (x : Tm a) (y : Tm b) :
    eval a
        (Tm.snd b a
          (Tm.pair b a (Tm.snd a b (Tm.pair a b x y)) (Tm.fst a b (Tm.pair a b x y))))
      = eval a x := rfl

-- NESTED projection beta on a pair-of-pairs. With `p : Tm (Ty.prod a b)` and
-- `q : Tm c`, the term `pair (prod a b) c p q : Tm (prod (prod a b) c)`. Projecting
-- `fst` (yielding `Tm (prod a b)`) then `fst` again recovers `fst p`; the inner
-- `fst` on the constructed pair beta-reduces to `eval (prod a b) p`, and the outer
-- `fst a b` wraps it identically on both sides. By `Tm.rec` iota + `Prod.fst`
-- projection; no domain axioms.
theorem eval_fst_fst (a b c : Ty) (p : Tm (Ty.prod a b)) (q : Tm c) :
    eval a (Tm.fst a b (Tm.fst (Ty.prod a b) c (Tm.pair (Ty.prod a b) c p q)))
      = eval a (Tm.fst a b p) := rfl

-- Dual nested projection on the RIGHT spine: with `p : Tm a` and
-- `q : Tm (Ty.prod b c)`, `snd` then `snd` of `pair a (prod b c) p q` recovers
-- `snd q`. By `Tm.rec` iota + `Prod.snd` projection; no domain axioms.
theorem eval_snd_snd (a b c : Ty) (p : Tm a) (q : Tm (Ty.prod b c)) :
    eval c (Tm.snd b c (Tm.snd a (Ty.prod b c) (Tm.pair a (Ty.prod b c) p q)))
      = eval c (Tm.snd b c q) := rfl

-- Mixed nesting (snd then fst): from `pair a (prod b c) p q`, the `snd` exposes the
-- inner `prod b c`, whose `fst` recovers `fst q`. By `Tm.rec` iota + `Prod`
-- projection (inner `snd` on the constructed pair, outer `fst b c` identical on both
-- sides); no domain axioms.
theorem eval_fst_snd (a b c : Ty) (p : Tm a) (q : Tm (Ty.prod b c)) :
    eval b (Tm.fst b c (Tm.snd a (Ty.prod b c) (Tm.pair a (Ty.prod b c) p q)))
      = eval b (Tm.fst b c q) := rfl

-- Mixed nesting (fst then snd), the dual of `eval_fst_snd`: from
-- `pair (prod a b) c p q`, the `fst` exposes the inner `prod a b`, whose `snd`
-- recovers `snd p`. By `Tm.rec` iota + `Prod` projection; no domain axioms.
theorem eval_snd_fst (a b c : Ty) (p : Tm (Ty.prod a b)) (q : Tm c) :
    eval b (Tm.snd a b (Tm.fst (Ty.prod a b) c (Tm.pair (Ty.prod a b) c p q)))
      = eval b (Tm.snd a b p) := rfl

-- ============================================================================
-- NAT ORDER extensions (Prop-level): successor-step facts of `Nat.le` / `Nat.lt`,
-- additive-LEFT monotonicity `a <= a + b`, and the DUAL mixed `Bvult` transitivity
-- (lt-then-le, the right-handed companion to the in-scope `Bvult_lt_of_le_left`).
--
-- Term-level `nle` TRUTH stays blocked (`eval (nle x y) = decide (Nat.le ..)` and
-- `decide` does NOT reduce), so these live at the `Nat` / `Bvult` Prop layer — the
-- layer the verifier's chained-comparison reasoning consumes.
--
-- `Nat.le` is the standard inductive (verified against clean-kernel/src/env/
-- inductive_fixed_indices.rs):
--   Nat.le : Nat -> Nat -> Prop  (num_params=1, 1 index)
--   Nat.le.refl : (n : Nat) -> Nat.le n n
--   Nat.le.step : (n m : Nat) -> Nat.le n m -> Nat.le n (Nat.succ m)
-- and `Nat.lt a b` is REDUCIBLE to `Nat.le (Nat.succ a) b`. All prelude lemmas
-- used (`Nat.le_refl`, `Nat.lt_of_lt_of_le`) are constructive `Declaration::Theorem`s
-- with empty axiom closure (#3551 / order_lemmas.rs); `Nat.le.refl`/`Nat.le.step`
-- are the canonical constructors (no axioms). No domain axioms.
-- ============================================================================

-- `n <= succ n`: one application of the `Nat.le.step` constructor to reflexivity.
-- `Nat.le.refl n : Nat.le n n`, then `Nat.le.step n n .. : Nat.le n (Nat.succ n)`.
-- Pure constructors of `Nat.le`, so the axiom closure is empty by construction
-- (the same shape the kernel's own `Nat.lt_succ_self` uses).
theorem nle_succ_self (n : Nat) : Nat.le n (Nat.succ n) :=
  Nat.le.step n n (Nat.le.refl n)

-- `n < succ n`: `Nat.lt n (Nat.succ n)` is `def`-reducible to
-- `Nat.le (Nat.succ n) (Nat.succ n)`, witnessed by `Nat.le_refl (Nat.succ n)`
-- (exactly the proof term the prelude's `Nat.lt_succ_self` carries). No axioms.
theorem nlt_succ_self (n : Nat) : Nat.lt n (Nat.succ n) :=
  Nat.le_refl (Nat.succ n)

-- Additive-LEFT bound: `a <= a + b` at every `b`, by `@Nat.rec` on `b`.
--   Base `b = 0`: `Nat.add a 0` reduces (iota, add recurses on its 2nd arg) to `a`,
--     so the goal is `Nat.le a a`, witnessed by `Nat.le_refl a`.
--   Step `b = succ k` with `ih : Nat.le a (Nat.add a k)`: `Nat.add a (succ k)`
--     reduces (iota) to `Nat.succ (Nat.add a k)`, so the goal is
--     `Nat.le a (Nat.succ (Nat.add a k))`, exactly `Nat.le.step a (Nat.add a k) ih`.
-- (`Nat.add x n` recurses on its 2nd arg: `add x 0 = x`, `add x (succ k) =
-- succ (add x k)`, so each iota reduction lands on the constructor's index.) No axioms.
theorem nadd_le_left (a b : Nat) : Nat.le a (Nat.add a b) :=
  @Nat.rec
    (fun k => Nat.le a (Nat.add a k))
    (Nat.le_refl a)
    (fun k ih => Nat.le.step a (Nat.add a k) ih)
    b

end TrustCore
"#;

/// Drive the real `clean check` pipeline (parse -> preprocess -> elaborate +
/// kernel-register) over a multi-declaration module, returning the populated
/// environment. Any parse / elaboration / kernel-check failure is an `Err`.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        // A `namespace` block collects inner-decl failures as `Failed` leaves
        // rather than propagating `Err`, so a swallowed failure must be surfaced
        // explicitly — otherwise a decl that fails to elaborate looks like a
        // false green.
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed to elaborate:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

/// Recursively gather `ElabResult::Failed` leaves (which a `namespace` block
/// produces instead of aborting) into human-readable `name: error` strings.
fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Resolve a declaration by its short (last-component) name to the exact `Name`
/// the environment registered it under — robust to namespace qualification
/// (`TrustCore.eval_band_tt`) without hard-coding the prefix.
fn resolve_name(env: &Environment, short: &str) -> Name {
    env.constants()
        .map(|c| &c.name)
        .find(|n| n.last_component().as_deref() == Some(short))
        .cloned()
        .unwrap_or_else(|| {
            let mut candidates: Vec<String> = env
                .constants()
                .map(|c| c.name.to_string())
                .filter(|s| s.contains("eval") || s.contains("TrustCore"))
                .collect();
            candidates.sort();
            panic!("no registered constant with short name `{short}`; TrustCore-ish names: {candidates:?}")
        })
}

/// Assert that `short` is registered AND proven down to the foundational axioms:
/// its transitive non-foundational axiom closure (which also surfaces any trust
/// marker) is empty.
fn assert_proven_to_foundations(env: &Environment, short: &str) {
    let name = resolve_name(env, short);
    let deps = env
        .axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name}: not registered (axiom_deps returned None)"));
    assert!(
        deps.is_empty(),
        "{name} must be proven down to the foundational axioms \
         (propext, Quot.sound, Classical.choice), but its transitive closure \
         still rests on non-foundational axioms / trust markers: {deps:?}"
    );
}

#[test]
fn trustcore_type_system_elaborates_and_kernel_checks() {
    elaborate_module(TRUSTCORE_SOURCE)
        .expect("the TrustCore type system + semantics must elaborate and kernel-check");
}

#[test]
fn trustcore_metatheorems_are_proven_down_to_the_foundational_axioms() {
    let env = elaborate_module(TRUSTCORE_SOURCE)
        .expect("the TrustCore module must elaborate before auditing its theorems");

    for thm in [
        "bvult_irrefl",
        "bvult_asymm",
        "bvult_trans",
        "bvand_testBit",
        "bvor_testBit",
        "bvxor_testBit",
        "bvadd_comm",
        "bvand_comm",
        "bvor_comm",
        "bvxor_comm",
        "eval_band_tt",
        "eval_band_ff",
        "eval_ite_tt",
        "eval_ite_ff",
        "eval_add",
        "eval_lit",
        "eval_ult",
        "eval_bnot_bnot",
        "eval_band_self",
        "eval_band_comm",
        "eval_land_comm",
        "eval_lor_comm",
        "eval_lxor_comm",
        "eval_add_comm",
        "eval_land_idem",
        "eval_lor_idem",
        "eval_nlit",
        "eval_nadd",
        "eval_nmul",
        "eval_nle",
        "eval_nadd_comm",
        "eval_nadd_assoc",
        "eval_band_assoc",
        "eval_nadd_zero_left",
        "eval_bor",
        "eval_bxor",
        "eval_bor_comm",
        "eval_bxor_comm",
        "eval_bor_self",
        "eval_bor_assoc",
        "bvand_assoc",
        "bvor_assoc",
        "eval_land_assoc",
        "eval_lor_assoc",
        "eval_bxor_self",
        "nmul_zero_left",
        "eval_nmul_zero_left",
        "add_right_comm",
        "nmul_succ_left",
        "nmul_comm",
        "nmul_one_left",
        "eval_nmul_comm",
        "demorgan_and",
        "demorgan_or",
        "absorb_and",
        "absorb_or",
        "band_true",
        "band_false",
        "bor_false",
        "bor_true",
        "eval_demorgan_and",
        "eval_demorgan_or",
        "eval_absorb_and",
        "eval_absorb_or",
        "eval_band_true",
        "eval_band_false",
        "eval_bor_false",
        "eval_bor_true",
        "nadd_zero_right",
        "nadd_succ_right",
        "nadd_succ_left",
        "nadd_right_comm",
        "eval_nadd_zero_right",
        "eval_nadd_right_comm",
        "bvxor_self",
        "eval_lxor_self",
        "eval_band_ff_right",
        "eval_band_tt_right",
        "eval_bor_ff_right",
        "eval_bor_tt_right",
        "eval_u",
        "eval_ite_unit_tt",
        "eval_ite_unit_ff",
        "nmul_add",
        "nmul_assoc",
        "eval_nmul_add",
        "eval_nmul_assoc",
        "eval_nmul_one",
        "nmul_zero_right",
        "nmul_succ_right",
        "nmul_one_right",
        "eval_nmul_zero_right",
        "eval_nmul_one_right",
        "shl_zero",
        "shl_succ",
        "bvshl_zero",
        "bvshl_shiftLeft_zero",
        "bxor_false_left",
        "bxor_true_left",
        "bxor_false_right",
        "bxor_true_right",
        "band_distrib_or",
        "bor_distrib_and",
        "band_distrib_xor",
        "eval_bxor_false_left",
        "eval_bxor_true_left",
        "eval_bxor_false_right",
        "eval_bxor_true_right",
        "eval_band_distrib_or",
        "eval_bor_distrib_and",
        "eval_band_distrib_xor",
        "nadd_mul",
        "eval_nadd_mul",
        "nmul_pos",
        "two_pow_pos",
        "shl_one",
        "bvshl_one",
        "two_mul",
        "bvshl_eq_bvadd_self",
        "nadd_le_mono_left",
        "nadd_le_mono_right",
        "nadd_le_mono",
        "Bvult_le",
        "Bvult_lt_of_le_left",
        "bvmul_comm",
        "eval_mul",
        "eval_mul_comm",
        "bvand_zero",
        "bvor_zero",
        "bvxor_zero",
        "nsub_zero",
        "nsub_succ",
        "zero_nsub",
        "eval_nsub",
        "eval_nsub_zero",
        "eval_fst_pair",
        "eval_snd_pair",
        "eval_inl",
        "eval_inr",
        "eval_some",
        "eval_none",
        "eval_pair",
        "eval_swap_pair",
        "eval_swap_pair_fst",
        "eval_swap_pair_snd",
        "eval_fst_fst",
        "eval_snd_snd",
        "eval_fst_snd",
        "eval_snd_fst",
        "nle_succ_self",
        "nlt_succ_self",
        "nadd_le_left",
        "eval_bnot",
        "eval_land",
        "eval_lor",
        "eval_lxor",
        "eval_sub",
        "bvand_idem",
        "bvor_idem",
    ] {
        assert_proven_to_foundations(&env, thm);
    }
}
