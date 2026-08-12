// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — runtime state and the arithmetic/container substrate (job **C3**).
//!
//! The machine this layer defines is **cell-addressed**, which is the one
//! deliberate structural departure from trust-ir's Lean reference semantics and
//! the reason a Clean-side semantics exists at all (see
//! [`super::eval_ir_syntax`]): a memory cell holds an [`IRScalar`], not a byte
//! string, so loading an enum-typed location needs no `Ty.byteSize` and the
//! `Ty::Enum => none` wall in `TrustIr/Semantics/Memory.lean:89-116` is designed
//! out rather than worked around.
//!
//! ## The value domain, and why the payload spine is inline
//!
//! Structured values — Rust structs, tuples, arrays and enum variants — are
//! held **inline** in `IRScalar` itself. `IRScalar.aggv sp` is an aggregate
//! whose fields are the `vnil` / `vcons` spine `sp`, and per the trust-ir
//! producer convention (`interpret.rs:1628-1684`) an enum stores its
//! discriminant at spine slot 0 and its selected variant's fields at slots
//! `1..`, so `ExtractField k` is uniformly "spine slot k" with no
//! record/variant special case anywhere in the semantics. Two reasons decide
//! that shape, in order of force:
//!
//! 1. The payload is a constructor of THIS family rather than an
//!    `IRList IRScalar` field, because a structural
//!    `IRScalar.agg : ListType IRScalar -> IRScalar` would be a NESTED
//!    inductive, which this elaborator does not register (the tree models
//!    nested and mutual families by object-level *encoding* instead —
//!    `rose_schema.rs`, `mutual_schema.rs`).
//!
//!    **MEASURED 2026-08-08, not assumed.** Probed through the scratchpad
//!    against the live spec:
//!
//!    ```text
//!    FAIL  inductive ProbeNested : Type
//!          | leaf : Nat -> ProbeNested
//!          | node : ListType ProbeNested -> ProbeNested     <- nested, REJECTED
//!
//!    PASS  inductive ProbeSpine : Type
//!          | leaf : Nat -> ProbeSpine
//!          | snil : ProbeSpine
//!          | scons : ProbeSpine -> ProbeSpine -> ProbeSpine  <- 2 recursive fields
//!          | agg   : ProbeSpine -> ProbeSpine
//!    ```
//!
//!    Both lines of that probe are the evidence FOR the present design: the
//!    nested route is closed, and the inline spine — direct recursion in the
//!    same family, including a constructor with two recursive fields — *does*
//!    elaborate. `IRScalar`'s `aggv` / `vnil` / `vcons` are exactly the
//!    `ProbeSpine` shape that passed.
//! 2. It settles aliasing by construction. Values are immutable: nothing ever
//!    rewrites an `IRScalar`, and `InsertField` builds a fresh `aggv` rather
//!    than updating one in place, so an aggregate read out of memory before a
//!    `Store` still denotes what it denoted then — with no deep copy on load
//!    and no aliasing question to answer.
//!
//! The price of the inline spine is junk inhabitants, named here rather than
//! left in a commit message: `vnil` and `vcons a b` are representable as
//! standalone values (storable, loadable, passable, returnable), and
//! `aggv (int_ 3)` is an aggregate with a non-spine payload. Every verdict on
//! them is fail-closed and stays inside the existing fault alphabet — the
//! pointer, aggregate and fnptr dispatches reject them with their existing
//! tags; `ir_vals_get` on a non-spine payload is `none`, hence `bad_field`;
//! `ir_vals_len` on one is zero, so `InsertField` fails its bounds check. No
//! theorem needs an `IRValueWF` predicate yet — the crystal's A2 premise is a
//! representation relation and constructs only well-formed values — but that
//! obligation is real and is recorded here.
//!
//! ## The integer model, and every consequence of it, named
//!
//! `IRScalar.int_` stores a non-negative `Nat` bit-pattern carrier, while every
//! integer instruction consumes its `IRTy` width. Constants and operands are
//! canonicalized modulo 2^w; arithmetic, signed/unsigned division/remainder,
//! shifts, bitwise operations, population count, comparisons, and integer
//! extension/truncation therefore have exact machine semantics. There is still
//! no float or byte-representation domain. Rather than let those remaining
//! gaps become quietly wrong answers, each one is a reachable, explicitly tagged
//! [`IROutcome.unmodelled`] result:
//!
//! | construct | verdict | fault tag |
//! |---|---|---|
//! | `Overflow` (all 3 ops) | unmodelled | `width_bounded` |
//! | `Cast` inttoptr / bitcast / transmute | unmodelled | `width_bounded` |
//! | `Cast` nullptr-to-int (no reserved null address) | unmodelled | `width_bounded` |
//! | `Cast` fptrunc/fpext/fptoui/fptosi/uitofp/sitofp/fptosisat/fptouisat | unmodelled | `float_domain` |
//! | `FCmp` (all 12 ops) | unmodelled | `float_domain` |
//! | `BinOp` fadd/fsub/fmul/fdiv/frem/fmin/fmax | unmodelled | `float_domain` |
//! | `UnOp` fneg/fabs/fsqrt/ffloor/fceil/ftrunc | unmodelled | `float_domain` |
//!
//! Kernel-executed differential vectors pin the exact width-bounded lane at
//! wrapping, sign boundaries, MIN/-1 and zero division UB, over-shift UB,
//! sign-fill, bitwise operations, population count, truncation, and both
//! extension modes. The crystal target's `Level::is_zero` itself performs no
//! arithmetic.
//!
//! Every decline has actionable repair options (v7/D3): float operations need
//! either a faithful IEEE carrier/differential oracle or lowering to proved bit
//! primitives; pointer/integer casts need either allocation provenance plus a
//! reserved null representation or an upstream non-emission proof;
//! bitcast/transmute need either byte-layout encode/decode semantics or typed
//! field lowering; and `Overflow` needs either its exact value-plus-flag carrier
//! or upstream decomposition into the exact operations above.
//!
//! Everything else — pointers, aggregates, enums, control flow, calls,
//! recursion, the panic arm — is modelled for real.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Register the `EvalIR` runtime state algebra and its arithmetic /
    /// container substrate.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_state(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_values()?;
        self.add_eval_ir_nat_helpers()?;
        self.add_eval_ir_containers()
    }

    /// The runtime value / machine / outcome inductives.
    fn add_eval_ir_values(&mut self) -> Result<(), SpecError> {
        // ── Values ──────────────────────────────────────────────────
        self.add_inductive(
            r"inductive IRScalar : Type
| undef_ : IRScalar
| bool_ : Bool → IRScalar
| int_ : Nat → IRScalar
| float_ : Nat → IRScalar
| unit_ : IRScalar
| ptr_ : Nat → IRScalar
| nullptr_ : IRScalar
| fat_ : Nat → Nat → IRScalar
| fnptr_ : Nat → IRScalar
| aggv : IRScalar → IRScalar
| vnil : IRScalar
| vcons : IRScalar → IRScalar → IRScalar",
            "EvalIR runtime values. Structured values are INLINE: `aggv sp` is a struct / tuple \
             / array / enum whose fields are the `vnil`/`vcons` spine `sp`, and per the trust-ir \
             producer convention (`interpret.rs:1628-1684`) an enum stores its discriminant at \
             spine slot 0 and its selected variant's fields at slots 1.. — so `ExtractField k` \
             is uniformly \"spine slot k\". The spine is part of THIS family, not an \
             `IRList IRScalar` field, which would be a NESTED inductive the elaborator does not \
             register. Values are immutable, so a value read out of memory before a Store still \
             denotes what it denoted then, with no deep copy and no aliasing question. \
             Ill-formed shapes (`aggv (int_ 3)`, a bare spine cell used as a value) are \
             representable; every dispatch gives them a fail-closed verdict, and representation \
             relations (crystal A2) construct only well-formed ones. `ptr_ a` is a pointer to \
             memory cell a; `nullptr_` is a SEPARATE constructor rather than address zero, so no \
             address computation can accidentally produce null. `fat_ d m` is a wide pointer \
             (data address, metadata). `float_` carries an opaque bit pattern that no operation \
             interprets.",
        )?;

        self.add_inductive(
            r"inductive IRBinding : Type
| mk : Nat → IRScalar → IRBinding",
            "One SSA binding: value id and its value. Locals are a cons list searched \
             head-first; since ids are minted fresh and monotonically, the first match is the \
             only match.",
        )?;

        self.add_inductive(
            r"inductive IRMemSlot : Type
| mk : Nat → IRScalar → Bool → IRMemSlot",
            "One memory cell: address, contents, liveness. A cell created by Alloca starts as \
             IRScalar.undef_, and loading undef_ is UB (the Lean model's \
             'reading uninitialized memory'), so uninitialised reads are caught rather than \
             silently producing a value.",
        )?;

        self.add_inductive(
            r"inductive IRFrame : Type
| mk : Nat → Nat → Nat → IRList IRBinding → IRList Nat → IRFrame",
            "One activation record: function id, current block id, program counter within that \
             block, locals, and the CALLER's declared result ids for this call — a list, because \
             trust_ir::InstrNode::results is a list and a multi-value return binds positionally. \
             Recursion is ordinary frame stacking; the crystal target Level::is_zero is \
             recursive, so this is load-bearing, not forward-compatibility.",
        )?;

        self.add_inductive(
            r"inductive IRMachine : Type
| mk : IRList IRFrame → IRList IRMemSlot → Nat → IRMachine",
            "The machine: frame stack (head = current), memory, next fresh address. There is \
             deliberately NO fresh-value-id counter: result ids come from the node that produced \
             them (see the IRNode registration), which is what makes a re-executed block bind \
             the same ids its own instructions refer to. There is no arena and no handle \
             counter: aggregates are inline values.",
        )?;

        // ── Faults and outcomes ─────────────────────────────────────
        //
        // A named fault alphabet rather than Nat codes: every fault site reads
        // as what it is, and unary Nat literals never appear in the semantics.
        self.add_inductive(
            r"inductive IRFault : Type
| no_frame : IRFault
| no_block : IRFault
| fetch_past_end : IRFault
| no_func : IRFault
| no_global : IRFault
| not_ptr : IRFault
| null_deref : IRFault
| bad_addr : IRFault
| uninit : IRFault
| not_bool : IRFault
| not_int : IRFault
| not_agg : IRFault
| bad_field : IRFault
| not_fnptr : IRFault
| assert_failed : IRFault
| unreachable : IRFault
| div_zero : IRFault
| div_overflow : IRFault
| shift_oob : IRFault
| negative : IRFault
| float_domain : IRFault
| width_bounded : IRFault
| bitlevel : IRFault",
            "Why an evaluation stopped. Split across three outcome kinds: `ub` (the program did \
             something undefined — null deref, out-of-bounds, uninitialised read, failed assert, \
             reaching Unreachable, division by zero/overflow, an out-of-range shift), \
             `type_error` (the IR is ill-formed for the \
             value it met), and `unmodelled` (the construct is outside the modelled fragment — \
             every occurrence is listed in this module's docs).",
        )?;

        self.add_inductive(
            r"inductive IROutcome : Type
| ret : IRList IRScalar → IROutcome
| ub : IRFault → IROutcome
| type_error : IRFault → IROutcome
| unmodelled : IRFault → IROutcome
| stuck : IRFault → IROutcome
| fuel_out : IROutcome",
            "The result of running a module. `ret` carries the outermost frame's returned \
             values. `unmodelled` is the honest verdict for a construct outside the modelled \
             fragment: it is NOT a value, so no theorem can accidentally rest on one.",
        )?;

        self.add_inductive(
            r"inductive IRConfig : Type
| running : IRMachine → IRConfig
| halted : IROutcome → IRConfig",
            "A machine configuration: still running, or halted with an outcome.",
        )?;

        self.add_inductive(
            r"inductive IRStepResult : Type
| value : IRScalar → IRStepResult
| fault : IROutcome → IRStepResult",
            "What a value-producing instruction yields: a value to bind, or a fault that halts \
             the machine. Keeps every ir_exec arm a single flat call.",
        )?;

        Ok(())
    }

    /// Boolean/arithmetic helpers over the foundation `Nat` and `Bool`.
    ///
    /// `Nat.add`, `Nat.sub` (truncating) and `Nat.pred` come from
    /// `add_foundation_types`; everything else EvalIR needs is built here so
    /// the stage stays independent of the `rec_env` / KExpr substrate.
    fn add_eval_ir_nat_helpers(&mut self) -> Result<(), SpecError> {
        // Two-level Nat.rec dispatch (the level_eqb idiom): the outer recursion
        // carries motive `Nat -> Bool` so the second argument stays free, and
        // the inner Nat.rec discriminates it. No nested match.
        self.add_recursive_def(
            concat!(
                "def ir_nat_eqb (a : Nat) (b : Nat) : Bool := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Bool) ",
                "(fun (y : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.true ",
                "(fun (_ : Nat) (_ : Bool) => Bool.false) y) ",
                "(fun (ap : Nat) (ih : Nat -> Bool) => fun (y : Nat) => ",
                "Nat.rec (fun (_ : Nat) => Bool) Bool.false ",
                "(fun (yp : Nat) (_ : Bool) => ih yp) y) ",
                "a b",
            ),
            "Boolean equality on Nat. EvalIR substrate (the spec's nat_eqb lives in the rec_env \
             stage, which EvalIR deliberately does not depend on).",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_ltb (a : Nat) (b : Nat) : Bool := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Bool) ",
                "(fun (y : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.false ",
                "(fun (_ : Nat) (_ : Bool) => Bool.true) y) ",
                "(fun (ap : Nat) (ih : Nat -> Bool) => fun (y : Nat) => ",
                "Nat.rec (fun (_ : Nat) => Bool) Bool.false ",
                "(fun (yp : Nat) (_ : Bool) => ih yp) y) ",
                "a b",
            ),
            "Strict less-than on Nat: zero < succ _, succ a < succ b iff a < b. EvalIR substrate.",
        )?;

        self.add_recursive_def(
            "def ir_nat_leb (a : Nat) (b : Nat) : Bool := Bool.or (ir_nat_ltb a b) (ir_nat_eqb a b)",
            "Less-or-equal on Nat. EvalIR substrate.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_mul (a : Nat) (b : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat) Nat.zero ",
                "(fun (_ : Nat) (ih : Nat) => Nat.add a ih) b",
            ),
            "Multiplication on Nat by repeated addition on the second argument. EvalIR substrate \
             (shl scales by a power of two).",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_pow2 (k : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat) (Nat.succ Nat.zero) ",
                "(fun (_ : Nat) (ih : Nat) => Nat.add ih ih) k",
            ),
            "Two to the k. EvalIR substrate: the modulus for exact width-k integer residues.",
        )?;

        // Division by repeated subtraction. The recursion is structural on an
        // explicit fuel argument because `a - b` is not structurally smaller
        // than `a`; `ir_nat_div` supplies `a` itself as the fuel, which is
        // always enough (the quotient never exceeds the dividend for b >= 1).
        self.add_recursive_def(
            concat!(
                "def ir_div_go (fuel : Nat) (a : Nat) (b : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Nat) ",
                "(fun (_ : Nat) => Nat.zero) ",
                "(fun (_ : Nat) (ih : Nat -> Nat) => fun (x : Nat) => ",
                "Bool.rec (fun (_ : Bool) => Nat) ",
                "(Nat.succ (ih (Nat.sub x b))) ",
                "Nat.zero ",
                "(ir_nat_ltb x b)) ",
                "fuel a",
            ),
            "Fuel-driven quotient by repeated subtraction. Bool.rec minor order is (false, true) \
             — the kernel declares Bool.false first — so the FIRST minor is the x >= b step and \
             the second is the x < b base. EvalIR substrate.",
        )?;

        self.add_recursive_def(
            "def ir_nat_div (a : Nat) (b : Nat) : Nat := ir_div_go a a b",
            "Truncating division on Nat, fuelled by the dividend. Callers must reject b = 0 \
             first (udiv/sdiv fault with ub div_zero); this definition returns a for b = 0 and \
             is never reached with it. EvalIR substrate.",
        )?;

        self.add_recursive_def(
            "def ir_nat_rem (a : Nat) (b : Nat) : Nat := Nat.sub a (ir_nat_mul b (ir_nat_div a b))",
            "Remainder as a - b*(a/b). Same zero-divisor precondition as ir_nat_div. EvalIR \
             substrate.",
        )?;

        self.add_recursive_def(
            "def ir_wrap (w : Nat) (n : Nat) : Nat := ir_nat_rem n (ir_nat_pow2 w)",
            "Canonical width-w machine-integer residue: n modulo 2^w. Unlike the earlier \
             unbounded-Nat approximation, this is the exact wrapping operation used by typed \
             integer Add/Sub/Mul in the authoritative EvalIR machine.",
        )?;

        self.add_recursive_def(
            "def ir_sub_wrap (w : Nat) (a : Nat) (b : Nat) : Nat := ir_wrap w (Nat.sub (Nat.add (ir_wrap w a) (ir_nat_pow2 w)) (ir_wrap w b))",
            "Exact wrapping subtraction on width-w residues. Adding one modulus before Nat.sub \
             represents the negative case without pretending Nat subtraction is machine \
             subtraction; the final ir_wrap returns the canonical residue.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bool_xor (a : Bool) (b : Bool) : Bool := ",
                "Bool.rec (fun (_ : Bool) => Bool) b (Bool.not b) a",
            ),
            "Exclusive or on Bool (Bool.rec minor order is false, true). EvalIR substrate for the \
             i1 case of BinOp::Xor.",
        )?;

        self.add_recursive_def(
            "def ir_bool_nat (value : Bool) : Nat := Bool.rec (fun (_ : Bool) => Nat) Nat.zero (Nat.succ Nat.zero) value",
            "Embed one Boolean bit as the Nat digit zero or one.",
        )?;

        self.add_recursive_def(
            "def ir_nat_bit (value : Nat) : Bool := ir_nat_eqb (ir_nat_rem value (Nat.succ (Nat.succ Nat.zero))) (Nat.succ Nat.zero)",
            "The low bit of a Nat, used only under an explicit machine width.",
        )?;

        self.add_recursive_def(
            "def ir_nat_double (value : Nat) : Nat := Nat.add value value",
            "Multiply a Nat by two without duplicating a recursive bit-operation call.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_bitop_go (op : Bool -> Bool -> Bool) (fuel : Nat) ",
                "(left : Nat) (right : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Nat -> Nat) ",
                "(fun (_ : Nat) (_ : Nat) => Nat.zero) ",
                "(fun (_ : Nat) (previous : Nat -> Nat -> Nat) => ",
                "fun (x : Nat) (y : Nat) => Nat.add ",
                "(ir_bool_nat (op (ir_nat_bit x) (ir_nat_bit y))) ",
                "(ir_nat_double (previous ",
                "(ir_nat_div x (Nat.succ (Nat.succ Nat.zero))) ",
                "(ir_nat_div y (Nat.succ (Nat.succ Nat.zero)))))) ",
                "fuel left right",
            ),
            "Width-fuelled, low-bit-first Boolean operation on Nat bit patterns.",
        )?;

        self.add_recursive_def(
            "def ir_nat_bitop (op : Bool -> Bool -> Bool) (width : Nat) (left : Nat) (right : Nat) : Nat := ir_nat_bitop_go op width (ir_wrap width left) (ir_wrap width right)",
            "Exact width-indexed integer And/Or/Xor substrate.",
        )?;

        self.add_recursive_def(
            "def ir_nat_bitnot (width : Nat) (value : Nat) : Nat := Nat.sub (Nat.pred (ir_nat_pow2 width)) (ir_wrap width value)",
            "Exact width-indexed integer complement: the all-ones mask minus the canonical input.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_ctpop_go (fuel : Nat) (value : Nat) : Nat := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Nat) (fun (_ : Nat) => Nat.zero) ",
                "(fun (_ : Nat) (previous : Nat -> Nat) => fun (x : Nat) => ",
                "Nat.add (ir_bool_nat (ir_nat_bit x)) ",
                "(previous (ir_nat_div x (Nat.succ (Nat.succ Nat.zero))))) ",
                "fuel value",
            ),
            "Count the set bits in exactly `fuel` low-order positions.",
        )?;

        self.add_recursive_def(
            "def ir_nat_ctpop (width : Nat) (value : Nat) : Nat := ir_nat_ctpop_go width (ir_wrap width value)",
            "Exact width-indexed population count.",
        )?;

        self.add_recursive_def(
            "def ir_sign_bit (width : Nat) (value : Nat) : Bool := ir_nat_leb (ir_nat_pow2 (Nat.pred width)) (ir_wrap width value)",
            "Whether the canonical width-bit pattern denotes a negative two's-complement value.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_signed_magnitude (width : Nat) (value : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) (ir_wrap width value) ",
                "(Nat.sub (ir_nat_pow2 width) (ir_wrap width value)) ",
                "(ir_sign_bit width value)",
            ),
            "Absolute magnitude of a width-bit two's-complement pattern.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_signed_encode (width : Nat) (negative : Bool) (magnitude : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) (ir_wrap width magnitude) ",
                "(ir_sub_wrap width Nat.zero magnitude) negative",
            ),
            "Encode a sign and non-negative magnitude as a canonical two's-complement pattern.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_signed_ltb (width : Nat) (left : Nat) (right : Nat) : Bool := ",
                "Bool.rec (fun (_ : Bool) => Bool) ",
                "(Bool.rec (fun (_ : Bool) => Bool) ",
                "(ir_nat_ltb (ir_wrap width left) (ir_wrap width right)) Bool.false ",
                "(ir_sign_bit width right)) ",
                "(Bool.rec (fun (_ : Bool) => Bool) Bool.true ",
                "(ir_nat_ltb (ir_wrap width left) (ir_wrap width right)) ",
                "(ir_sign_bit width right)) ",
                "(ir_sign_bit width left)",
            ),
            "Exact signed less-than on width-bit two's-complement patterns: differing signs decide \
             immediately; equal signs preserve the canonical unsigned ordering.",
        )?;

        Ok(())
    }

    /// Monomorphic container helpers.
    ///
    /// Each is a single `IRList.rec` — or, for the three payload-spine
    /// walkers, a single `IRScalar.rec`, because an aggregate's fields are a
    /// `vnil` / `vcons` chain inside `IRScalar` rather than a separate list —
    /// with a function-valued motive where a second argument has to stay free,
    /// the `listGet` idiom already used by `schema.rs`. They are monomorphic
    /// because the spec's own list helpers are
    /// (`list_length : ListType KExpr -> Nat`), and a polymorphic definition
    /// buys nothing here.
    fn add_eval_ir_containers(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_nats_get (l : IRList Nat) (k : Nat) : IROption Nat := ",
                "IRList.rec Nat (fun (_ : IRList Nat) => Nat -> IROption Nat) ",
                "(fun (_ : Nat) => IROption.none Nat) ",
                "(fun (x : Nat) (_ : IRList Nat) (ih : Nat -> IROption Nat) => fun (j : Nat) => ",
                "Nat.rec (fun (_ : Nat) => IROption Nat) (IROption.some Nat x) ",
                "(fun (jp : Nat) (_ : IROption Nat) => ih jp) j) ",
                "l k",
            ),
            "Positional lookup into a Nat list. EvalIR container helper.",
        )?;

        // The three payload-spine walkers. Each is an explicit `IRScalar.rec`
        // with a function-valued motive rather than a `match`: the spine is a
        // constructor family of IRScalar itself, so a match would have to name
        // all twelve constructors AND fix the index argument, and the index has
        // to stay free for the inner `Nat.rec` to discriminate it.
        self.add_recursive_def(
            concat!(
                "def ir_vals_get (l : IRScalar) (k : Nat) : IROption IRScalar := ",
                "IRScalar.rec (fun (_ : IRScalar) => Nat -> IROption IRScalar) ",
                "(fun (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Bool) (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Nat) (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Nat) (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Nat) (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Nat) (_ : Nat) (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : Nat) (_ : Nat) => IROption.none IRScalar) ",
                "(fun (_ : IRScalar) (_ : Nat -> IROption IRScalar) (_ : Nat) => ",
                "IROption.none IRScalar) ",
                "(fun (_ : Nat) => IROption.none IRScalar) ",
                "(fun (x : IRScalar) (_ : IRScalar) (_ : Nat -> IROption IRScalar) ",
                "(ih : Nat -> IROption IRScalar) => fun (j : Nat) => ",
                "Nat.rec (fun (_ : Nat) => IROption IRScalar) (IROption.some IRScalar x) ",
                "(fun (jp : Nat) (_ : IROption IRScalar) => ih jp) j) ",
                "l k",
            ),
            "Positional lookup into an inline payload spine: slot k of the vnil/vcons chain that \
             an aggv carries. A non-spine payload (aggv (int_ 3)) has length zero and no field \
             at any index, so ExtractField on it is bad_field and InsertField on it fails the \
             bounds check — the fail-closed reading of an ill-formed value. EvalIR container \
             helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_vals_set (l : IRScalar) (k : Nat) (v : IRScalar) : IRScalar := ",
                "IRScalar.rec (fun (_ : IRScalar) => Nat -> IRScalar) ",
                "(fun (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Bool) (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) (_ : Nat) (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : IRScalar) (_ : Nat -> IRScalar) (_ : Nat) => IRScalar.vnil) ",
                "(fun (_ : Nat) => IRScalar.vnil) ",
                "(fun (x : IRScalar) (rest : IRScalar) (_ : Nat -> IRScalar) ",
                "(ih : Nat -> IRScalar) => fun (j : Nat) => ",
                "Nat.rec (fun (_ : Nat) => IRScalar) (IRScalar.vcons v rest) ",
                "(fun (jp : Nat) (_ : IRScalar) => IRScalar.vcons x (ih jp)) j) ",
                "l k",
            ),
            "Functional positional update of an inline payload spine. Out-of-range leaves the \
             spine unchanged in length — InsertField checks the index against ir_vals_len \
             separately and faults with bad_field, so the silent case is unreachable from the \
             semantics. A non-spine payload (aggv (int_ 3)) collapses to vnil, and that case is \
             unreachable for the same reason: its length is zero, so the bounds check rejects \
             every index first. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_vals_len (l : IRScalar) : Nat := ",
                "IRScalar.rec (fun (_ : IRScalar) => Nat) ",
                "Nat.zero ",
                "(fun (_ : Bool) => Nat.zero) ",
                "(fun (_ : Nat) => Nat.zero) ",
                "(fun (_ : Nat) => Nat.zero) ",
                "Nat.zero ",
                "(fun (_ : Nat) => Nat.zero) ",
                "Nat.zero ",
                "(fun (_ : Nat) (_ : Nat) => Nat.zero) ",
                "(fun (_ : Nat) => Nat.zero) ",
                "(fun (_ : IRScalar) (_ : Nat) => Nat.zero) ",
                "Nat.zero ",
                "(fun (_ : IRScalar) (_ : IRScalar) (_ : Nat) (ihr : Nat) => Nat.succ ihr) ",
                "l",
            ),
            "Length of an inline payload spine: the number of vcons cells. A non-spine payload \
             (aggv (int_ 3)) has length zero and no field at any index, so ExtractField on it is \
             bad_field and InsertField on it fails the bounds check — the fail-closed reading of \
             an ill-formed value. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nodes_get (l : IRList IRNode) (k : Nat) : IROption IRNode := ",
                "IRList.rec IRNode (fun (_ : IRList IRNode) => Nat -> IROption IRNode) ",
                "(fun (_ : Nat) => IROption.none IRNode) ",
                "(fun (x : IRNode) (_ : IRList IRNode) (ih : Nat -> IROption IRNode) => ",
                "fun (j : Nat) => Nat.rec (fun (_ : Nat) => IROption IRNode) ",
                "(IROption.some IRNode x) ",
                "(fun (jp : Nat) (_ : IROption IRNode) => ih jp) j) ",
                "l k",
            ),
            "Fetch the node at a program counter. Running off the end returns none, which \
             ir_step turns into stuck fetch_past_end — a block without a terminator does not \
             fall through. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_block_find (l : IRList IRBlock) (k : Nat) : IROption IRBlock := ",
                "IRList.rec IRBlock (fun (_ : IRList IRBlock) => IROption IRBlock) ",
                "(IROption.none IRBlock) ",
                "(fun (b : IRBlock) (_ : IRList IRBlock) (ih : IROption IRBlock) => ",
                "IRBlock.rec (fun (_ : IRBlock) => IROption IRBlock) ",
                "(fun (i : Nat) (_ : IRList Nat) (_ : IRList IRNode) => ",
                "Bool.rec (fun (_ : Bool) => IROption IRBlock) ih (IROption.some IRBlock b) ",
                "(ir_nat_eqb i k)) b) l",
            ),
            "Find a block by id. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_func_find (l : IRList IRFunc) (k : Nat) : IROption IRFunc := ",
                "IRList.rec IRFunc (fun (_ : IRList IRFunc) => IROption IRFunc) ",
                "(IROption.none IRFunc) ",
                "(fun (f : IRFunc) (_ : IRList IRFunc) (ih : IROption IRFunc) => ",
                "IRFunc.rec (fun (_ : IRFunc) => IROption IRFunc) ",
                "(fun (i : Nat) (_ : IRList Nat) (_ : Nat) (_ : IRList IRBlock) => ",
                "Bool.rec (fun (_ : Bool) => IROption IRFunc) ih (IROption.some IRFunc f) ",
                "(ir_nat_eqb i k)) f) l",
            ),
            "Find a function by id. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_global_find (l : IRList IRGlobal) (k : Nat) : IROption IRGlobal := ",
                "IRList.rec IRGlobal (fun (_ : IRList IRGlobal) => IROption IRGlobal) ",
                "(IROption.none IRGlobal) ",
                "(fun (g : IRGlobal) (_ : IRList IRGlobal) (ih : IROption IRGlobal) => ",
                "IRGlobal.rec (fun (_ : IRGlobal) => IROption IRGlobal) ",
                "(fun (i : Nat) (_ : IRConst) => ",
                "Bool.rec (fun (_ : Bool) => IROption IRGlobal) ih (IROption.some IRGlobal g) ",
                "(ir_nat_eqb i k)) g) l",
            ),
            "Find a global by id. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_case_find (l : IRList IRSwitchCase) (k : Nat) : IROption IRSwitchCase := ",
                "IRList.rec IRSwitchCase (fun (_ : IRList IRSwitchCase) => IROption IRSwitchCase) ",
                "(IROption.none IRSwitchCase) ",
                "(fun (c : IRSwitchCase) (_ : IRList IRSwitchCase) (ih : IROption IRSwitchCase) => ",
                "IRSwitchCase.rec (fun (_ : IRSwitchCase) => IROption IRSwitchCase) ",
                "(fun (v : Nat) (_ : Nat) (_ : IRList Nat) => ",
                "Bool.rec (fun (_ : Bool) => IROption IRSwitchCase) ih ",
                "(IROption.some IRSwitchCase c) (ir_nat_eqb v k)) c) l",
            ),
            "Find the Switch arm matching a selector value; none means take the default. EvalIR \
             container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_binding_lookup (l : IRList IRBinding) (k : Nat) : IROption IRScalar := ",
                "IRList.rec IRBinding (fun (_ : IRList IRBinding) => IROption IRScalar) ",
                "(IROption.none IRScalar) ",
                "(fun (b : IRBinding) (_ : IRList IRBinding) (ih : IROption IRScalar) => ",
                "IRBinding.rec (fun (_ : IRBinding) => IROption IRScalar) ",
                "(fun (i : Nat) (v : IRScalar) => ",
                "Bool.rec (fun (_ : Bool) => IROption IRScalar) ih (IROption.some IRScalar v) ",
                "(ir_nat_eqb i k)) b) l",
            ),
            "Look up an SSA value id in a locals list, head-first. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_mem_lookup (l : IRList IRMemSlot) (a : Nat) : IROption IRMemSlot := ",
                "IRList.rec IRMemSlot (fun (_ : IRList IRMemSlot) => IROption IRMemSlot) ",
                "(IROption.none IRMemSlot) ",
                "(fun (s : IRMemSlot) (_ : IRList IRMemSlot) (ih : IROption IRMemSlot) => ",
                "IRMemSlot.rec (fun (_ : IRMemSlot) => IROption IRMemSlot) ",
                "(fun (i : Nat) (_ : IRScalar) (_ : Bool) => ",
                "Bool.rec (fun (_ : Bool) => IROption IRMemSlot) ih (IROption.some IRMemSlot s) ",
                "(ir_nat_eqb i a)) s) l",
            ),
            "Find the memory cell at an address. EvalIR container helper.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_mem_update (l : IRList IRMemSlot) (a : Nat) (v : IRScalar) : IRList IRMemSlot := ",
                "IRList.rec IRMemSlot (fun (_ : IRList IRMemSlot) => IRList IRMemSlot) ",
                "(IRList.nil IRMemSlot) ",
                "(fun (s : IRMemSlot) (rest : IRList IRMemSlot) (ih : IRList IRMemSlot) => ",
                "IRMemSlot.rec (fun (_ : IRMemSlot) => IRList IRMemSlot) ",
                "(fun (i : Nat) (old : IRScalar) (live : Bool) => ",
                "Bool.rec (fun (_ : Bool) => IRList IRMemSlot) ",
                "(IRList.cons IRMemSlot s ih) ",
                "(IRList.cons IRMemSlot (IRMemSlot.mk i v live) rest) ",
                "(ir_nat_eqb i a)) s) l",
            ),
            "Write a value into the cell at an address, preserving liveness and every other \
             cell. Store checks the address exists and is live first, so the no-match case is \
             unreachable from the semantics. EvalIR container helper.",
        )?;

        Ok(())
    }
}
