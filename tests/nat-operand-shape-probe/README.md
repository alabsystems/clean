# Nat operand-shape probe

Which `Nat` operations does **Lean's** kernel grind on, and at which operand
position — measured, not reasoned about.

```bash
python3 tests/nat-operand-shape-probe/run.py
```

Exit code is non-zero when any probe's measured verdict differs from the
`probe-expect` pinned in its header.

## Why this exists

Clean's kernel has `native_nat_binop_grind_stuck`
(`clean-kernel/src/tc/reduction/nat.rs`), a guard that leaves
`Nat.{add,sub,mul,pow}` stuck rather than unfolding a Θ(literal) unary tower.
Its rationale claimed the guard "matches Lean, whose `@[extern]`
`Nat.add`/`Nat.sub` stay stuck on a symbolic operand". **That is half false**,
and the cost of not knowing was large: the spec routes every comparison through
`ir_nat_ltb a b := ir_nat_pos (Nat.sub b a)`, so seven exported declarations
type-checked in Clean *only* because of that guard, and the foreign-kernel
cross-check could not check them at all. (**Closed 2026-09-08**: both
comparisons now peel one `Nat.rec` layer off each operand before subtracting,
so `sub_lit_second` is never the major premise Lean has to reduce; the gate is
green. The matrix below is still the reason.)

Three separate attempts to fix it were built on operand-shape assumptions that
turned out to be wrong, each costing a full spec build or a 24 MB export cycle
to discover. This corpus makes the assumption cheap to check: **~150 ms per
probe.**

## The comparison shapes, added 2026-09-08 (lean 4.30.0-rc2)

Seven probes mirror the spec's comparison vocabulary (`ir_nat_sub_ltb` /
`ir_nat_sub_eqb`, the subtraction tests; `ir_nat_ltb` / `ir_nat_eqb`, the
peeled comparisons) and force each as the major premise of a `Bool.rec`, which
is the shape every reflected predicate and every `icmp` puts it in:

| probe | shape | verdict |
|---|---|---|
| `cmp_old_eqb_sym_u32` | old `ir_nat_eqb` major at `ir_br_c1`: `iszero (Nat.sub x 4294967295)` | **GRIND** |
| `cmp_old_ltb_f64_sym` | old `ir_nat_ltb` with the literal first (`ir_f64_class`'s NaN test) | **GRIND** |
| `cmp_peel_eqb_sym_u32` / `_u32_sym` | peeled `ir_nat_eqb`, either orientation | stuck-fast |
| `cmp_peel_ltb_sym_f64` / `_f64_sym` | peeled `ir_nat_ltb`, either orientation | stuck-fast |
| `cmp_peel_eqb_succsym_u32` | peeled `ir_nat_eqb (Nat.succ x) 4294967295` | **GRIND** |

The last row is the limit of the peel, pinned on purpose: a SUCCESSOR-HEADED
symbolic operand passes the peel and exposes `Nat.sub x 4294967294` again. The
peel makes a comparison's reducibility depend on the operands' HEADS, not on
which side the literal sits; it is not a universal guard. The reflected
predicates never produce that shape (their operands are `ir_wrap` residues,
stuck or literal), which is why `gate::leancross` is green on it.

## The matrix, as of 2026-08-31 (lean 4.30.0-rc2)

**Exactly one combination grinds** (of the six operation/position pairs; the
comparison-shape rows above add the two spec-level shapes built on it).

| probe | 512 | u32 (4.29e9) | f64 (9.22e18) |
|---|---|---|---|
| `sub_lit_second` | **GRIND** 16.5 s | **GRIND** | **GRIND** |
| `sub_lit_first` | stuck-fast | stuck-fast | stuck-fast |
| `add_lit_first` / `add_lit_second` | stuck-fast | stuck-fast | stuck-fast |
| `mul_lit_second` | stuck-fast | stuck-fast | stuck-fast |
| `pow_lit_second` | stuck-fast | stuck-fast | stuck-fast |
| `ble_lit_first` | stuck-fast | stuck-fast | stuck-fast |

`Nat.sub` recurses structurally on its **second** argument. Put a large literal
there with a symbolic first operand and Lean walks it. Every other op, and
`sub` with the literal on the *other* side, declines in O(1).

Note the 512 row: it is the SLOWEST, at 16.5 s, because it genuinely walks 512
steps. The u32 and f64 rows return in ~190 ms only because `maxRecDepth 4096`
stops them early. **A fast failure is not a small one.**

## The forcer, and why the obvious probes do not work

Two weaker designs were tried first and both measured nothing:

1. **A per-op defining equation** (`Nat.sub a (succ b) = Nat.pred (Nat.sub a b)`).
   That is a ONE-STEP reduction — everything converged in ~150 ms and the
   matrix was uniformly green. It also used a single identity for all six ops,
   which is only true for `sub`/`ble`/`beq`; `add`/`mul`/`pow` "failed" because
   the TEST was false, not the kernel.
2. **Both operands closed** (`Nat.sub 0 <big> = 0`). Lean's GMP path decides
   those instantly. Uniformly green, again measuring nothing.

What works is the shape the export actually hit: a **recursor whose major
premise is the op application**, with **one operand symbolic**. `Nat.rec` forces
its major to whnf, the native path is unavailable because an operand is open,
and the kernel recurses once per unit of the literal.

The probe statements are deliberately **not all true**. We are measuring whether
the kernel GRINDS trying or DECLINES fast — `STUCK-fast` is a refusal in
milliseconds and is the safe outcome; `GRIND` means it blew a limit.

## Adding a probe

```lean
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
--@ probe-expect: STUCK-fast     -- STUCK-fast | GRIND | OK
theorem probe (x : Nat) : @Nat.rec (fun _ => Bool) Bool.false (fun _ _ => Bool.true) (<op application>) = Bool.false := rfl
```

Keep one symbolic operand. A probe with both operands closed measures the GMP
path and tells you nothing about this asymmetry.

## Output

`run.py` writes `matrix.json` beside itself: one row per probe with its pinned
expectation, the measured verdict and the wall time. It is **gitignored on
purpose**. The expectations that the gate enforces live in the `--@ probe-expect:`
headers of `probes/*.lean`, and those are tracked; `matrix.json` only restates them
alongside timings that move every run. A tracked file that runner output rewrites is
the failure mode `CLAUDE.md` records for `data/suite_state/`, so this one stays out
of the index.
