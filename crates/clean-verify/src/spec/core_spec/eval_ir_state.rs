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
//! extension/truncation therefore have exact machine semantics. There is no
//! byte-representation domain, and until 2026-08-15 there was no float domain
//! either. Rather than let those remaining gaps become quietly wrong answers,
//! each one is a reachable, explicitly tagged [`IROutcome.unmodelled`] result:
//!
//! | construct | verdict | fault tag |
//! |---|---|---|
//! | `Overflow` (all 3 ops) | unmodelled | `width_bounded` |
//! | `Cast` inttoptr / transmute | unmodelled | `width_bounded` |
//! | **`Cast` bitcast** | **PARTLY MODELLED — see below** | `width_bounded` outside it |
//! | `Cast` nullptr-to-int (no reserved null address) | unmodelled | `width_bounded` |
//! | `Cast` fptrunc/fpext/fptoui/fptosi/uitofp/sitofp/fptosisat/fptouisat | unmodelled | `float_domain` |
//! | `FCmp` (all 12 ops) | unmodelled | `float_domain` |
//! | **`BinOp` fadd/fsub/fmul** | **MODELLED on the classified AND the finite fragment** | `float_domain` outside it |
//! | **`BinOp` fdiv** | **MODELLED on the classified fragment only** | `float_domain` outside it |
//! | `BinOp` frem/fmin/fmax | unmodelled | `float_domain` |
//! | `UnOp` fneg/fabs/fsqrt/ffloor/fceil/ftrunc | unmodelled | `float_domain` |
//!
//! **The row that changed, 2026-08-15.** [`super::eval_ir_float`] gives the
//! four float arithmetic operators a real binary64 evaluation on the fragment
//! where IEEE 754 fixes the answer from the operands' CLASSIFICATION alone —
//! infinities, signed zeros, and the exact-zero sum `x + (-x)` — and keeps the
//! tagged `unmodelled` verdict for NaN payloads, invalid operations, anything
//! needing round-to-nearest-even, and every binary format but binary64. That
//! module states what is modelled, what is refused, and the MEASURED reason the
//! finite case cannot be added in this substrate without buying speed with
//! trust.
//!
//! **And again, 2026-08-16: the FINITE fragment, for three of the four.**
//! [`super::eval_ir_bits`] rewrites the significand arithmetic O(bit-length) —
//! a restoring division and a doubling ladder over the same `Nat.add` /
//! `Nat.sub` this stage already uses, so no accelerated constant is added — and
//! [`super::eval_ir_float_fin`] is correctly-rounded binary64 `fadd` / `fsub` /
//! `fmul` built on it: round-to-nearest-even over the 53-bit significand, exact
//! subnormals, exact signed zeros, exact overflow to infinity. `fdiv` stays
//! refused on the finite fragment, with its own measurement. The 2026-08-15
//! claim that the finite case *cannot* be added in this substrate was right
//! about `ir_nat_div` and `ir_nat_mul` as they are written and wrong about the
//! substrate. Nothing that used to evaluate changed; strictly more evaluates.
//!
//! **The second row that changed, 2026-08-16 (the TENTH chain).** `bitcast` was
//! a blanket `ir_width_fault`, and the reason given — a cell-addressed model
//! has no representation to reinterpret — is still exactly right for the cases
//! it was written about. It does not cover the only bitcast the shipped kernel
//! emits: `i32 -> u32`, two INTEGER types at the SAME width, where
//! `IRScalar.int_ n` already IS the canonical width-`w` bit pattern and nothing
//! is reinterpreted. `ir_bitcast_eval` decides exactly that fragment. A width
//! mismatch is still `ir_width_fault`; a float or pointer on either side is
//! still `ir_width_fault`, because `ir_ty_int_width` declines them — so
//! `bitcast f64 -> u64` is as refused as it ever was; and `transmute` is a
//! different constructor and is untouched, so `transmute::<f64, u64>`, the
//! counterexample the original refusal names, is unaffected.
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
//!
//! ## The `ir_wrap` literal-folding lemma (2026-08-15)
//!
//! `ir_wrap w n` is `ir_nat_rem n (ir_nat_pow2 w)`, and `ir_nat_div` fuels
//! `ir_div_go` with its own dividend. Until this lane the loop's guard was
//! `ir_nat_ltb x b`, a PAIRED UNARY WALK: deciding `57343 < 2^64` peeled 57,343
//! `Nat.rec` layers off both operands. Nothing else in the residue is expensive
//! — for `n < 2^w` the quotient is zero, so the loop body never runs and the
//! `Nat.sub` / `ir_nat_mul` around it are O(1) — which is why a width-w residue
//! measured as O(DIVIDEND). The wall that put on the record was:
//!
//! * `ir_wrap ir_d64 (ir_wrap ir_d64 57343)`, the residue `is_valid_char`'s
//!   left-constant `icmp` forces, cost **24 s** in `ir_vc_split1`.
//! * `ir_wrap ir_d32 (ir_wrap ir_d32 4294967295)` — the `expr_bvar_in_range`
//!   sentinel — extrapolated to **~9.6 days**, so that chain carries PATH
//!   witnesses and no concrete `ir_eval` at any argument.
//!
//! **The lemma, and it is a theorem about all of `Nat`, not about literals**
//! (stated here in the vocabulary it landed with; the names moved when the
//! comparisons themselves were folded — see the next section):
//!
//! ```text
//! ir_nat_ltb_sub_eq : forall (a b : Nat),
//!     Eq Bool (ir_nat_pos (Nat.sub b a)) (ir_nat_ltb a b)
//! ```
//!
//! `a < b` iff `b - a` is a successor. `Nat.sub` on two closed literals is
//! reduced NATIVELY by the kernel on `BigNat` — the same acceleration
//! `ir_nat_rem`'s outer `Nat.sub` and `ir_nat_pow2`'s `Nat.add` have relied on
//! since this stage was written, so the substrate acquires no new accelerated
//! constant and no new trust — and `ir_nat_pos` decides on the first iota step.
//! `ir_div_go` now takes that guard, and `ir_div_go_guard` restates the loop's
//! unfolding equation with the walk back in it, so "the loop is unchanged"
//! is kernel-checked rather than read off two definitions.
//!
//! Why this shape and not the other two on the table: a REWRITE lemma cannot
//! help, because the cost is paid inside the kernel's own whnf of a machine
//! execution, where there is no place to apply one; and re-expressing
//! `ir_nat_rem` as the kernel-native `Nat.mod` would have folded in O(log) but
//! would have ASSERTED (never proved) that the fuel loop and the native
//! primitive agree, adding an accelerated constant with a body the kernel never
//! consults. This route proves its one equation and leaves the arithmetic
//! exactly where it was.
//!
//! **Measured, EvalIR bundle, one declaration each** (`Eq Nat (ir_wrap w …) …`
//! proved by `Eq.refl`), the "before" column in one process against the old
//! guard and the "after" column in one process against this one:
//!
//! ```text
//!                                     before          after
//! w=64  n=57343          single        14.923 s       0.009 s   both measured
//! w=64  n=57343          double        24.973 s       0.010 s   both measured
//! w= 8  n=300   (q=1)                   0.096 s       0.004 s   both measured
//! w=64  n=1114112        double     not measured      0.010 s   (the record's
//!                                                               nearest measured
//!                                                               point is 439.8 s
//!                                                               to decide ir_vc_c3
//!                                                               at one argument)
//! w=32  n=4294967295     double     ~9.6 days,        0.007 s
//!                                   EXTRAPOLATED, never measured — the
//!                                   sentinel wall this lemma removes
//! ```
//!
//! **The cost law is now linear in the QUOTIENT and independent of the
//! dividend** — measured at w=8, where `n/256` is 216 / 432 / 864: 0.080 s /
//! 0.159 s / 0.325 s (x1.99, x2.04), against 0.005 s for the same dividend
//! 55,296 at w=16, where the quotient is 0. That supersedes the
//! "linear in the dividend" law of 2026-08-14 (which itself corrected a "2^W"
//! law), and both earlier laws remain TRUE of the definition they were measured
//! on — this one changed the definition.
//!
//! Residues are unchanged, checked by differential witnesses rather than
//! asserted: 255/8→255, 256/8→0, 257/8→1, 10/3→2, 5/0→0, 7/1→1,
//! `ir_nat_div 17 5 = 3`, `ir_nat_rem 17 5 = 2`, `ir_nat_rem 7 0 = 7`.
//!
//! **What it is worth on a whole build, and the claim that buys.** Four
//! replicates each side, the four heavy gates launched together so both sets
//! run at matched 4-way concurrency: a full `Specification::new()` goes from
//! 1600.0 / 1600.4 / 1608.0 / 1610.4 s to 1540.4 / 1546.5 / 1548.7 / 1556.3 s —
//! **56.7 s of wall and 56.4 s of CPU, 3.5%, with the two distributions
//! disjoint.** That number is also a CORRECTION: `docs/CRYSTAL_STATUS.md`
//! brackets the sixth and seventh chains at "about 11 minutes … concentrated in
//! one place: the width-64 residue of 57,343", and removing that residue
//! entirely is worth 57 s, not 668 s. The residue is real and it is ~25 s once
//! per build, exactly as the standalone measurement says; the rest of the
//! bracket is the two stages' other ~60 declarations. The EvalIR flavour GAINS
//! 0.7 s (7.1 → 7.8 s): it carries the five new declarations and forces no
//! large residue, because those chains are Full-only stages.
//!
//! **What this lemma did NOT fix, named so the next lane did not assume it.**
//! `ir_nat_ltb` and `ir_nat_eqb` still peeled their FIRST operand one `Nat.rec`
//! layer at a time. Every residue is a constant and now folds; an ARGUMENT did
//! not, so a concrete `ir_eval` over `is_valid_char` cost about its code point
//! (0.065 s at 65, 19.1 s at 0xD800, 31.4 s at 70,000, 210.1 s at 0x110000 —
//! all measured, all passing, and all but the first declined on cost), and the
//! fifth chain's sentinel-true path still needed 4.29e9 `ir_nat_eqb` steps.
//! That was the named next build item. It is the next section.
//!
//! ## Folding the comparisons themselves (2026-08-15, later)
//!
//! The same technique, applied where the previous lane said it had to be: to
//! the comparison rather than to the division guard. It is a DEFINITIONAL
//! RESTRUCTURING plus kernel-checked equations, not a rewrite:
//!
//! * the two paired unary walks are kept verbatim under `ir_nat_ltb_walk` /
//!   `ir_nat_eqb_walk` (plus `ir_nat_leb_walk`), where nothing calls them;
//! * `ir_nat_ltb` / `ir_nat_eqb` / `ir_nat_leb` — the names the machine and
//!   every reflected predicate use, unchanged at every call site — now decide
//!   through `Nat.sub`;
//! * three theorems say those are the SAME PREDICATES at every pair of
//!   arguments:
//!
//! ```text
//! ir_nat_ltb_walk_eq : forall (a b : Nat), Eq Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b)
//! ir_nat_eqb_walk_eq : forall (a b : Nat), Eq Bool (ir_nat_eqb a b) (ir_nat_eqb_walk a b)
//! ir_nat_leb_walk_eq : forall (a b : Nat), Eq Bool (ir_nat_leb a b) (ir_nat_leb_walk a b)
//! ```
//!
//! `a < b` is `ir_nat_pos (b - a)`; `a = b` is `a - b = 0 AND b - a = 0`, as a
//! `Bool.rec` over `ir_nat_iszero`. `ir_nat_ltb_walk_eq` is the landed lemma
//! with its two roles exchanged, `ir_nat_eqb_walk_eq` is the same induction —
//! `Nat.rec` on `a` with the motive generalized over `b`, `ir_nat_sub_zero_left`
//! at the zero case, `ir_nat_sub_succ_succ` twice at the successor case —
//! and `ir_nat_leb_walk_eq` is one `ir_eq_cong` per disjunct. No new accelerated
//! constant: `Nat.sub` was already here.
//!
//! **Seven restatements make the swap auditable where it is CASHED, not only
//! where it is proved.** `ir_div_go_guard` restates the division loop with the
//! walk as its guard, and `ir_icmp_{ult,ugt,ule,uge,eq,ne}_walk`
//! ([`super::eval_ir_ops`]) restate all six integer `icmp` arms: the
//! instruction the machine executes, at any width and any operands, answers
//! exactly what the paired unary walk answers on the two canonical residues.
//!
//! **Measured — what it unblocked.** Full spec, per-declaration wall clock, and
//! the baseline re-measured in the same window on the same box so the ratio is
//! not carried over from another one:
//!
//! ```text
//!                                              walk        folded
//! ir_eval is_valid_char (int_ 55296)          3.071 s      0.016 s
//! ir_eval is_valid_char (int_ 70000)          5.045 s      0.017 s
//! ir_eval is_valid_char (int_ 1114112)       33.752 s      0.016 s
//! ir_eval bvar_in_range (3, 1, u32::MAX)   >2857 s, KILLED 0.010 s
//! ir_eval bvar_in_range (0, 1, u32::MAX)   not attempted   0.010 s
//! ```
//!
//! All five are now REGISTERED. The first three are the three the previous lane
//! wrote, kernel-checked and declined at 19.106 / 31.404 / 210.144 s on a
//! loaded box. The fourth is the fifth chain's sentinel-true path, which had no
//! concrete witness at ANY argument in this program's history: the baseline ran
//! it for **47 min 37 s without returning** and was killed. Both `condbr`
//! chains now cover every emitted edge concretely as well as by PATH witness.
//!
//! **Measured — what it COST, because it is a cost and not a saving.** Three
//! paired rounds, two replicates per side launched TOGETHER so both share one
//! window at matched 4-way concurrency (sequential rounds on this box drift by
//! 20 s and cannot support a 5 s claim):
//!
//! ```text
//!            before (wall / user CPU)        after (wall / user CPU)
//! round 1    218.984 218.985 / 210.71 210.81   224.349 224.291 / 216.10 216.15
//! round 2    210.102 209.901 / 205.89 205.58   214.963 215.279 / 210.67 210.82
//! round 3    216.634 217.085 / 210.36 210.82   221.619 221.945 / 215.29 215.70
//! ```
//!
//! **+5.13 s of wall and +5.10 s of CPU on a ~215 s `Specification::new()` —
//! +2.4%, every round agreeing in sign and within 0.4 s in magnitude.** Not a
//! 3.5% saving like the wrap lemma: the opposite sign, and the honest reason is
//! that the wrap lemma removed cost from declarations that were already
//! registered while this one buys declarations that were not.
//!
//! **Where the 5 s goes, measured rather than attributed.** A per-stage clock
//! over all 160 stages, both trees, one window: exactly ONE stage moved —
//! `add_eval_ir_contains`, 1.822 → 7.034 s at the SAME 28 declarations — and
//! inside it `ir_fc_exact` 0.893 → 3.700 s, `ir_fc_never_faults` 0.449 →
//! 2.874 s, `ir_fc_machine_sound` 0.460 → 2.866 s. That chain's A4 is an
//! `Eq.refl` at SYMBOLIC bytes (`ir_fc_exact`: "the machine's answer is a term
//! in them"), and its predicate's head is `ir_nat_eqb`. A subtraction equality
//! test necessarily names BOTH operands TWICE — `a - b` and `b - a` — where the
//! walk names each once, so the stuck term the kernel compares structurally is
//! about twice the size. The 55 other `ir_wrap`-carrying declarations moved by
//! less than 0.3 s each in either direction. `add_eval_ir_valid_char` went
//! DOWN, 0.651 → 0.512 s, while gaining three executions.
//!
//! **The alternative, priced.** Folding `ir_nat_ltb` alone buys all three
//! `is_valid_char` witnesses (that body's three comparisons are all `ult`) at
//! no measurable cost, and leaves the fifth chain's fourth path PATH-only. The
//! trade taken here is 5.1 s per full spec build for two executions of an
//! emitted `condbr` edge that no argument could reach before. Both agreement
//! theorems are proved either way — a theorem costs nothing; it is the
//! DEFINITION the machine runs that costs, and that choice is the measurement
//! above.

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
        // The O(bit-length) substrate, AFTER the helpers it is built on
        // (`ir_nat_ltb`, `ir_nat_pow2`, `ir_eq_cong`) and the reference
        // definitions its differential ladder runs against (`ir_nat_div`,
        // `ir_nat_rem`, `ir_nat_mul`). See [`super::eval_ir_bits`].
        self.add_eval_ir_bits()?;
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
             (data address, metadata). `float_` carries an IEEE 754 binary64 bit pattern; as of \
             2026-08-15 it is no longer opaque — super::eval_ir_float CLASSIFIES it (NaN / \
             infinity / signed zero / finite) and the four float arithmetic operators compute on \
             the fragment that classification determines. It is still not interpreted as a \
             rational: no rounding, no significand arithmetic, and everything outside the \
             classified fragment is the tagged unmodelled outcome.",
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
| bitlevel : IRFault
| not_float : IRFault",
            "Why an evaluation stopped. Split across three outcome kinds: `ub` (the program did \
             something undefined — null deref, out-of-bounds, uninitialised read, failed assert, \
             reaching Unreachable, division by zero/overflow, an out-of-range shift), \
             `type_error` (the IR is ill-formed for the \
             value it met), and `unmodelled` (the construct is outside the modelled fragment — \
             every occurrence is listed in this module's docs). \
             \n\n`not_float` was APPENDED on 2026-08-15 with the binary64 value domain \
             (super::eval_ir_float). Appended, not inserted, so no constructor's position moves. \
             It exists because that domain has two different refusals that must stay \
             distinguishable: `type_error not_float` is ill-formed IR (a float instruction met an \
             integer operand or a non-float type), while `unmodelled float_domain` is well-formed \
             IR whose answer this semantics declines to invent (a NaN payload, an invalid \
             operation, a rounding). Collapsing them would make the two indistinguishable in \
             every theorem that reads an outcome.",
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
        // ---------------------------------------------------------------
        // THE SHARED-VOCABULARY RULE. Every declaration reachable from
        // `add_eval_ir` is elaborated in TWO environments: the spec
        // foundation (`new_eval_ir_spec`) and Clean's Lean-4 production
        // prelude (`new_eval_ir_prelude_spec`, the composition boundary Trust
        // binds its program artifacts in). It may therefore name only what
        // BOTH carry — `Eq`/`Eq.refl`/`Eq.symm`/`Eq.trans`/`Eq.subst`, `Nat`,
        // `Bool`, their recursors — plus its own `ir_*`. The foundation's
        // `Eq.cong` and `nat_sub_*` lemmas are NOT in the Lean prelude (Lean
        // spells congruence `congrArg`, with a different argument order, and
        // has no `0 - k = 0`), so the two congruence/subtraction facts this
        // stage needs are proved HERE, from the shared vocabulary, under
        // `ir_` names — the same precedent as `ir_nat_eqb` duplicating
        // `nat_eqb`.
        // ---------------------------------------------------------------
        self.add_recursive_def(
            concat!(
                "def ir_eq_cong (A : Type) (B : Type) (f : A -> B) (x : A) (y : A) ",
                "(h : Eq A x y) : Eq B (f x) (f y) := ",
                "Eq.subst A (fun (z : A) => Eq B (f x) (f z)) x y h (Eq.refl B (f x))",
            ),
            "Congruence: x = y implies f x = f y. The foundation proves this as `Eq.cong` from \
             based `Eq.rec`; this is the same fact proved from `Eq.subst`, which is the ONE \
             transport primitive carried with an identical argument order by both the spec \
             foundation and the Lean prelude. Every congruence step in the EvalIR stage goes \
             through it, so the stage names no environment-specific vocabulary. DerivedProved, \
             zero axiom_deps.",
        )?;

        // ---------------------------------------------------------------
        // The two O(1) decision primitives every folded comparison ends in.
        // ---------------------------------------------------------------
        self.add_recursive_def(
            concat!(
                "def ir_nat_pos (n : Nat) : Bool := ",
                "Nat.rec (fun (_ : Nat) => Bool) Bool.false ",
                "(fun (_ : Nat) (_ : Bool) => Bool.true) n",
            ),
            "Is this Nat a successor? One Nat.rec, no walk: the kernel peels a literal to \
             `Nat.succ (n-1)` in O(1) and this recursor ignores both the predecessor and the \
             induction hypothesis, so it decides on the FIRST iota step whatever the value. \
             EvalIR substrate for ir_nat_ltb.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_iszero (n : Nat) : Bool := ",
                "Nat.rec (fun (_ : Nat) => Bool) Bool.true ",
                "(fun (_ : Nat) (_ : Bool) => Bool.false) n",
            ),
            "Is this Nat zero? `ir_nat_pos`'s complement, written directly rather than as \
             `Bool.not (ir_nat_pos n)` so it decides in ONE iota step instead of two. EvalIR \
             substrate for ir_nat_eqb.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_sub_zero_left (k : Nat) : Eq Nat (Nat.sub Nat.zero k) Nat.zero := ",
                "Nat.rec (fun (m : Nat) => Eq Nat (Nat.sub Nat.zero m) Nat.zero) ",
                "(Eq.refl Nat Nat.zero) ",
                "(fun (m : Nat) (ih : Eq Nat (Nat.sub Nat.zero m) Nat.zero) => ",
                "ir_eq_cong Nat Nat Nat.pred (Nat.sub Nat.zero m) Nat.zero ih) k",
            ),
            "0 - k = 0, by Nat.rec on k and ir_eq_cong Nat.pred (Nat.sub recurses on its SECOND \
             argument, so the successor case is `Nat.pred (Nat.sub 0 m)`, and `Nat.pred 0` is \
             `0` by iota). A duplicate of the foundation stage's `nat_sub_zero_left` under an \
             `ir_` name for the same reason `ir_nat_eqb` duplicates `nat_eqb`: that one lives \
             in add_foundation_arith_lemmas, which the dependency-scoped EvalIr bundle does \
             not carry — and the Lean prelude has no `0 - k = 0` at all. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_sub_succ_succ (a : Nat) (b : Nat) : ",
                "Eq Nat (Nat.sub (Nat.succ a) (Nat.succ b)) (Nat.sub a b) := ",
                "Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.sub (Nat.succ a) (Nat.succ k)) (Nat.sub a k)) ",
                "(Eq.refl Nat a) ",
                "(fun (k : Nat) ",
                "(ih : Eq Nat (Nat.sub (Nat.succ a) (Nat.succ k)) (Nat.sub a k)) => ",
                "ir_eq_cong Nat Nat Nat.pred ",
                "(Nat.sub (Nat.succ a) (Nat.succ k)) (Nat.sub a k) ih) b",
            ),
            "(succ a) - (succ b) = a - b, by Nat.rec on b and ir_eq_cong Nat.pred — Nat.sub \
             recurses on its SECOND argument, so the symbolic successor case needs induction \
             rather than Eq.refl. A duplicate of the foundation stage's `nat_sub_succ_succ` \
             under an `ir_` name, for the same reason as ir_nat_sub_zero_left above: neither \
             the dependency-scoped EvalIr bundle nor the Lean prelude carries it. \
             DerivedProved, zero axiom_deps.",
        )?;

        // ---------------------------------------------------------------
        // THE PAIRED UNARY WALKS — the reference vocabulary.
        //
        // These are the definitions `ir_nat_eqb` / `ir_nat_ltb` had until
        // 2026-08-15, kept verbatim under `_walk` names. Nothing in the
        // semantics calls them: they exist so that the folded comparisons
        // below have something to be PROVED EQUAL TO, and so that every
        // restating theorem (`ir_div_go_guard`, the six `ir_icmp_*_walk`)
        // can put the walk predicate back into the statement of what the
        // machine runs. See the module doc.
        //
        // Two-level Nat.rec dispatch (the level_eqb idiom): the outer
        // recursion carries motive `Nat -> Bool` so the second argument stays
        // free, and the inner Nat.rec discriminates it. No nested match.
        // ---------------------------------------------------------------
        self.add_recursive_def(
            concat!(
                "def ir_nat_eqb_walk (a : Nat) (b : Nat) : Bool := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Bool) ",
                "(fun (y : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.true ",
                "(fun (_ : Nat) (_ : Bool) => Bool.false) y) ",
                "(fun (ap : Nat) (ih : Nat -> Bool) => fun (y : Nat) => ",
                "Nat.rec (fun (_ : Nat) => Bool) Bool.false ",
                "(fun (yp : Nat) (_ : Bool) => ih yp) y) ",
                "a b",
            ),
            "Boolean equality on Nat as a PAIRED UNARY WALK — the reference definition, kept \
             so `ir_nat_eqb_walk_eq` has a theorem to state. It peels its FIRST operand one \
             Nat.rec layer at a time, which is what made a concrete is_valid_char run cost \
             about its code point. EvalIR substrate (the spec's nat_eqb lives in the rec_env \
             stage, which EvalIR deliberately does not depend on).",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_ltb_walk (a : Nat) (b : Nat) : Bool := ",
                "Nat.rec (fun (_ : Nat) => Nat -> Bool) ",
                "(fun (y : Nat) => Nat.rec (fun (_ : Nat) => Bool) Bool.false ",
                "(fun (_ : Nat) (_ : Bool) => Bool.true) y) ",
                "(fun (ap : Nat) (ih : Nat -> Bool) => fun (y : Nat) => ",
                "Nat.rec (fun (_ : Nat) => Bool) Bool.false ",
                "(fun (yp : Nat) (_ : Bool) => ih yp) y) ",
                "a b",
            ),
            "Strict less-than on Nat as a PAIRED UNARY WALK: zero < succ _, succ a < succ b \
             iff a < b. The reference definition, kept so `ir_nat_ltb_walk_eq` has a theorem \
             to state; nothing in the semantics calls it. EvalIR substrate.",
        )?;

        // ---------------------------------------------------------------
        // THE FOLDED COMPARISONS — what the machine actually runs, and the
        // three agreement theorems that say they are the same predicates.
        // See the module doc for the measurement.
        // ---------------------------------------------------------------
        self.add_recursive_def(
            "def ir_nat_ltb (a : Nat) (b : Nat) : Bool := ir_nat_pos (Nat.sub b a)",
            "`a < b`, decided through truncated subtraction instead of a paired unary walk, \
             and PROVED equal to that walk by ir_nat_ltb_walk_eq. On two closed literals the \
             kernel reduces `Nat.sub` NATIVELY on BigNat (the same acceleration `ir_nat_rem`'s \
             outer `Nat.sub` and `ir_nat_pow2`'s `Nat.add` have always relied on), so this \
             costs one native subtraction and one iota step where the walk costs min(a,b) of \
             them. It adds no accelerated constant to the substrate: `Nat.sub` was already \
             here. On a symbolic operand it is stuck exactly where the walk is stuck.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_eqb (a : Nat) (b : Nat) : Bool := ",
                "Bool.rec (fun (_ : Bool) => Bool) Bool.false ",
                "(ir_nat_iszero (Nat.sub b a)) (ir_nat_iszero (Nat.sub a b))",
            ),
            "`a = b`, decided as `a - b = 0 AND b - a = 0` instead of a paired unary walk, and \
             PROVED equal to that walk by ir_nat_eqb_walk_eq. Bool.rec's minor order is \
             (false, true), so the FIRST minor is the `a - b` non-zero case (answer false) and \
             the SECOND is the case where it vanished (answer: did `b - a` vanish too). Both \
             subtractions are native on closed literals and each `ir_nat_iszero` decides on \
             the first iota step, so the u32 sentinel pair — 4.29e9 walk steps — costs two \
             BigNat subtractions. Adds no accelerated constant: `Nat.sub` was already here.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_ltb_walk_eq (a : Nat) (b : Nat) : ",
                "Eq Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b) := ",
                "Nat.rec (fun (x : Nat) => forall (y : Nat), ",
                "Eq Bool (ir_nat_ltb x y) (ir_nat_ltb_walk x y)) ",
                "(fun (y : Nat) => Eq.refl Bool (ir_nat_ltb_walk Nat.zero y)) ",
                "(fun (x : Nat) (ih : forall (y : Nat), ",
                "Eq Bool (ir_nat_ltb x y) (ir_nat_ltb_walk x y)) => fun (y : Nat) => ",
                "Nat.rec (fun (z : Nat) => ",
                "Eq Bool (ir_nat_ltb (Nat.succ x) z) (ir_nat_ltb_walk (Nat.succ x) z)) ",
                "(ir_eq_cong Nat Bool ir_nat_pos (Nat.sub Nat.zero (Nat.succ x)) Nat.zero ",
                "(ir_nat_sub_zero_left (Nat.succ x))) ",
                "(fun (z : Nat) (_ : Eq Bool (ir_nat_ltb (Nat.succ x) z) ",
                "(ir_nat_ltb_walk (Nat.succ x) z)) => ",
                "Eq.trans Bool (ir_nat_ltb (Nat.succ x) (Nat.succ z)) ",
                "(ir_nat_ltb x z) (ir_nat_ltb_walk (Nat.succ x) (Nat.succ z)) ",
                "(ir_eq_cong Nat Bool ir_nat_pos (Nat.sub (Nat.succ z) (Nat.succ x)) ",
                "(Nat.sub z x) (ir_nat_sub_succ_succ z x)) ",
                "(ih z)) y) a b",
            ),
            "THE LESS-THAN LEMMA: the subtraction test the machine runs and the paired unary \
             walk are the SAME PREDICATE, at every pair of arguments. Nat.rec on a with the \
             motive generalized over b; the zero case is Eq.refl (`ir_nat_ltb_walk 0 y` and \
             `ir_nat_pos (Nat.sub y 0)` are the same recursor application after delta), the \
             successor case splits on b: at 0 through ir_nat_sub_zero_left, at succ z through \
             ir_nat_sub_succ_succ and the induction hypothesis. Nothing here is about literals — \
             it is a theorem about all of Nat, and the speed is what the kernel does with it \
             afterwards. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_eqb_walk_eq (a : Nat) (b : Nat) : ",
                "Eq Bool (ir_nat_eqb a b) (ir_nat_eqb_walk a b) := ",
                "Nat.rec (fun (x : Nat) => forall (y : Nat), ",
                "Eq Bool (ir_nat_eqb x y) (ir_nat_eqb_walk x y)) ",
                "(fun (y : Nat) => ir_eq_cong Nat Bool ",
                "(fun (k : Nat) => Bool.rec (fun (_ : Bool) => Bool) Bool.false ",
                "(ir_nat_iszero (Nat.sub y Nat.zero)) (ir_nat_iszero k)) ",
                "(Nat.sub Nat.zero y) Nat.zero (ir_nat_sub_zero_left y)) ",
                "(fun (x : Nat) (ih : forall (y : Nat), ",
                "Eq Bool (ir_nat_eqb x y) (ir_nat_eqb_walk x y)) => fun (y : Nat) => ",
                "Nat.rec (fun (z : Nat) => ",
                "Eq Bool (ir_nat_eqb (Nat.succ x) z) (ir_nat_eqb_walk (Nat.succ x) z)) ",
                "(Eq.refl Bool Bool.false) ",
                "(fun (z : Nat) (_ : Eq Bool (ir_nat_eqb (Nat.succ x) z) ",
                "(ir_nat_eqb_walk (Nat.succ x) z)) => ",
                "Eq.trans Bool (ir_nat_eqb (Nat.succ x) (Nat.succ z)) (ir_nat_eqb x z) ",
                "(ir_nat_eqb_walk (Nat.succ x) (Nat.succ z)) ",
                "(Eq.trans Bool (ir_nat_eqb (Nat.succ x) (Nat.succ z)) ",
                "(Bool.rec (fun (_ : Bool) => Bool) Bool.false (ir_nat_iszero (Nat.sub z x)) ",
                "(ir_nat_iszero (Nat.sub (Nat.succ x) (Nat.succ z)))) (ir_nat_eqb x z) ",
                "(ir_eq_cong Nat Bool (fun (k : Nat) => Bool.rec (fun (_ : Bool) => Bool) ",
                "Bool.false (ir_nat_iszero k) ",
                "(ir_nat_iszero (Nat.sub (Nat.succ x) (Nat.succ z)))) ",
                "(Nat.sub (Nat.succ z) (Nat.succ x)) (Nat.sub z x) (ir_nat_sub_succ_succ z x)) ",
                "(ir_eq_cong Nat Bool (fun (k : Nat) => Bool.rec (fun (_ : Bool) => Bool) ",
                "Bool.false (ir_nat_iszero (Nat.sub z x)) (ir_nat_iszero k)) ",
                "(Nat.sub (Nat.succ x) (Nat.succ z)) (Nat.sub x z) (ir_nat_sub_succ_succ x z))) ",
                "(ih z)) y) a b",
            ),
            "THE EQUALITY LEMMA, the same shape and the same three ingredients as \
             ir_nat_ltb_walk_eq: the two-sided subtraction test the machine runs and the \
             paired unary walk are the SAME PREDICATE at every pair of arguments. Nat.rec on a \
             with the motive generalized over b. The zero case is NOT Eq.refl — unlike the \
             less-than lemma it needs ir_nat_sub_zero_left, because `0 - y` sits under the \
             Bool.rec scrutinee and does not reduce at a symbolic y; once it is 0 the \
             scrutinee is true and the true minor is `ir_nat_iszero (y - 0)`, which IS the \
             walk's zero minor after delta. The successor case splits on b: at 0 both sides \
             are Bool.false by iota, at succ z two ir_eq_congs move both subtractions down \
             through ir_nat_sub_succ_succ and the induction hypothesis finishes. DerivedProved, \
             zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_nat_leb (a : Nat) (b : Nat) : Bool := Bool.or (ir_nat_ltb a b) (ir_nat_eqb a b)",
            "Less-or-equal on Nat. EvalIR substrate. Unchanged text, and folded for free: both \
             disjuncts are now the subtraction tests.",
        )?;

        self.add_recursive_def(
            "def ir_nat_leb_walk (a : Nat) (b : Nat) : Bool := Bool.or (ir_nat_ltb_walk a b) (ir_nat_eqb_walk a b)",
            "Less-or-equal as a paired unary walk — the reference vocabulary for ir_nat_leb, \
             so the `ule` / `uge` icmp arms have a walk-worded statement to be proved equal \
             to. Nothing in the semantics calls it.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_nat_leb_walk_eq (a : Nat) (b : Nat) : ",
                "Eq Bool (ir_nat_leb a b) (ir_nat_leb_walk a b) := ",
                "Eq.trans Bool (ir_nat_leb a b) ",
                "(Bool.or (ir_nat_ltb_walk a b) (ir_nat_eqb a b)) (ir_nat_leb_walk a b) ",
                "(ir_eq_cong Bool Bool (fun (g : Bool) => Bool.or g (ir_nat_eqb a b)) ",
                "(ir_nat_ltb a b) (ir_nat_ltb_walk a b) (ir_nat_ltb_walk_eq a b)) ",
                "(ir_eq_cong Bool Bool (fun (g : Bool) => Bool.or (ir_nat_ltb_walk a b) g) ",
                "(ir_nat_eqb a b) (ir_nat_eqb_walk a b) (ir_nat_eqb_walk_eq a b))",
            ),
            "Less-or-equal agrees with its walk, one ir_eq_cong per disjunct over the two \
             primitive lemmas. Stated rather than left implicit because ir_nat_leb is what the \
             `ule` / `uge` icmp arms and ir_trunc_int's width check call. DerivedProved, zero \
             axiom_deps.",
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
        //
        // The guard is `ir_nat_ltb`, which is now the subtraction test;
        // `ir_nat_ltb_walk_eq` proves it IS the paired unary walk, and
        // `ir_div_go_guard` below restates this loop's unfolding equation in
        // terms of that walk so the substitution is a kernel-checked fact
        // rather than a reading of two definitions.
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
             the second is the x < b base. The guard is ir_nat_ltb, which is the subtraction \
             test, and that is the literal-folding lemma cashed in: the loop is IDENTICAL to \
             the walk-guarded one (see ir_div_go_guard) but each guard costs one native BigNat \
             subtraction instead of min(x,b) Nat.rec unfoldings, which is what made a width-w \
             residue cost O(dividend). EvalIR substrate.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_div_go_guard (fuel : Nat) (a : Nat) (b : Nat) : ",
                "Eq Nat (ir_div_go (Nat.succ fuel) a b) ",
                "(Bool.rec (fun (_ : Bool) => Nat) ",
                "(Nat.succ (ir_div_go fuel (Nat.sub a b) b)) Nat.zero (ir_nat_ltb_walk a b)) := ",
                "ir_eq_cong Bool Nat (fun (g : Bool) => Bool.rec (fun (_ : Bool) => Nat) ",
                "(Nat.succ (ir_div_go fuel (Nat.sub a b) b)) Nat.zero g) ",
                "(ir_nat_ltb a b) (ir_nat_ltb_walk a b) (ir_nat_ltb_walk_eq a b)",
            ),
            "The division loop's unfolding equation, stated with the paired unary walk as the \
             guard. This is what makes the guard swap auditable rather than trusted: one \
             ir_eq_cong over ir_nat_ltb_walk_eq shows that the loop this specification runs \
             takes exactly the step the strict-less-than walk loop took — `x < b` returns zero, \
             otherwise one plus the loop on `x - b`. Nothing downstream of ir_div_go changed \
             meaning, and this theorem is where that claim is checked. DerivedProved, zero \
             axiom_deps.",
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
