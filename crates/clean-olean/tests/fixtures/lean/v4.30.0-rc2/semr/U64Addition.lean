/- Copyright 2026 Andrew Yates. Apache-2.0.
   Exact original serialized scalar-leaf semantics, not Rust source admission. -/
import SemRMiniRust
namespace SemRU64Addition
open SemR
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Literal bytes of the ORIGINAL compiler Module. The canonical writer chooses
    its minimum required version; this actual closed scalar body is v38. -/
def originalBytes : List Nat := [84, 82, 85, 83, 84, 95, 73, 82, 38, 0, 0, 0, 5, 31, 115, 111, 117, 114, 99, 101, 95, 119, 111, 114, 100, 54, 52, 95, 97, 100, 100, 105, 116, 105, 111, 110, 95, 111, 114, 105, 103, 105, 110, 97, 108, 18, 97, 114, 109, 54, 52, 45, 97, 112, 112, 108, 101, 45, 109, 97, 99, 111, 115, 120, 81, 47, 85, 115, 101, 114, 115, 47, 97, 121, 97, 116, 101, 115, 47, 116, 114, 117, 115, 116, 45, 116, 104, 105, 114, 45, 119, 111, 114, 100, 54, 52, 45, 97, 100, 100, 105, 116, 105, 111, 110, 45, 50, 48, 50, 54, 49, 49, 48, 55, 45, 110, 102, 117, 45, 52, 115, 116, 114, 53, 115, 104, 112, 47, 105, 110, 112, 117, 116, 115, 47, 111, 114, 105, 103, 105, 110, 97, 108, 46, 114, 115, 8, 97, 100, 100, 105, 116, 105, 111, 110, 1, 120, 0, 1, 1, 8, 1, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 0, 1, 0, 8, 3, 25, 8, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 41, 0, 0, 0, 0, 8, 0, 1, 1, 2, 0, 1, 0, 1, 26, 0, 0, 20, 1, 2, 0, 0, 1, 0, 1, 45, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 1, 1, 0, 4, 0, 0, 0, 0, 1, 1, 8, 0, 0, 2, 1, 2, 0, 0, 0, 0]

/-- Full v63 spelling produced separately by the canonical writer, not the
    historical compiler artifact and not a patched header. -/
def currentBytes : List Nat := [84, 82, 85, 83, 84, 95, 73, 82, 63, 0, 0, 0, 5, 31, 115, 111, 117, 114, 99, 101, 95, 119, 111, 114, 100, 54, 52, 95, 97, 100, 100, 105, 116, 105, 111, 110, 95, 111, 114, 105, 103, 105, 110, 97, 108, 18, 97, 114, 109, 54, 52, 45, 97, 112, 112, 108, 101, 45, 109, 97, 99, 111, 115, 120, 81, 47, 85, 115, 101, 114, 115, 47, 97, 121, 97, 116, 101, 115, 47, 116, 114, 117, 115, 116, 45, 116, 104, 105, 114, 45, 119, 111, 114, 100, 54, 52, 45, 97, 100, 100, 105, 116, 105, 111, 110, 45, 50, 48, 50, 54, 49, 49, 48, 55, 45, 110, 102, 117, 45, 52, 115, 116, 114, 53, 115, 104, 112, 47, 105, 110, 112, 117, 116, 115, 47, 111, 114, 105, 103, 105, 110, 97, 108, 46, 114, 115, 8, 97, 100, 100, 105, 116, 105, 111, 110, 1, 120, 0, 1, 1, 8, 1, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 0, 1, 0, 8, 3, 25, 8, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 41, 0, 0, 0, 0, 8, 0, 1, 1, 2, 0, 1, 0, 1, 26, 0, 0, 20, 1, 2, 0, 0, 1, 0, 1, 45, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 8, 0, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def signature : FuncTy := ⟨[.int .u64], [.int .u64], false⟩
def body (literal : Nat) : Block :=
  ⟨0, [(0, .int .u64)], [⟨.const (.int .u64) (.int literal), [1]⟩,
    ⟨.binop .add (.int .u64) 0 1, [2]⟩, ⟨.ret [2], []⟩]⟩
def function (literal : Nat) : Func :=
  { id := 0, ty := 0, entry := 0, blocks := [body literal], name := [97,100,100,105,116,105,111,110] }
def module (literal : Nat) : Module :=
  { funcTys := [signature], enums := [], functions := [function literal],
    target := some ⟨[97,114,109,54,52,45,97,112,112,108,101,45,109,97,99,111,115,120], 8, false, none, 2⟩ }

/-- Kernel reduction of the COMPLETE original encoding, not an assumed digest
    or a reconstructed fragment made equal only by a claim. -/
theorem original_decodes : decode originalBytes = .ok (module 7) := rfl

theorem current_decodes : decode currentBytes = .ok (module 7) := rfl

private theorem pure_ok {α : Type} (value : α) : (pure value : R α) = .ok value := rfl

def initial (literal input depth : Nat) (memory : Mem) : Core :=
  { fn := function literal, sig := signature, block := body literal,
    pc := 0, env := [(0, .int .u64 input)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := memory }

theorem start_exact (literal input depth : Nat) (inputValid : input < modulus 64) :
    start (module literal) 0 [.int .u64 input] depth =
      .ok (initial literal input depth Mem.empty) := by
  simp [start, module, function, signature, body, initial, checkSig, bindParams,
    expectTy, Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.executableTarget,
    findBlock, nth?, rejectPoison, ok_bind, inputValid] <;> rfl

/-- Full64 inputs and arbitrary initial allocation memory. No stack access,
    external call, frame assumption or postulated successful-run premise. -/
theorem run_exact (literal input depth : Nat) (memory : Mem)
    (inputValid : input < modulus 64) :
    run (module literal) 3 (initial literal input depth memory) =
      .ret [.int .u64 ((input + literal) % modulus 64)] := by
  simp [run, stepCore, execNode, initial, body, module, function, signature,
    nth?, constStep, constVal, binopStep, evalBinop, intBin, liftOp,
    pure_ok, ok_bind, getV, getVs, lookupEnv, expectTy, rejectPoison, expectInt, isBoolTy,
    Val.ty, Ty.beq, IntTy.code, IntTy.bits, Module.pointerBits,
    bindResults, next, ofR, retStep, returnTo, checkSig, inputValid,
    Nat.mod_lt _ (by decide : 0 < modulus 64)]

/-- Every valid original U64 input reaches the exact canonical return. The
    decoder statement above binds the entire compiler encoding to this body. -/
theorem original_return (input depth : Nat) (inputValid : input < modulus 64) :
    runFunction (module 7) 0 [.int .u64 input] 3 depth =
      .ret [.int .u64 ((input + 7) % modulus 64)] := by
  simp only [runFunction, start_exact 7 input depth inputValid]
  exact run_exact 7 input depth Mem.empty inputValid

/-- Successful canonical execution excludes UB/panic at EVERY finite reachable
    prefix, by the existing relational theorem. No source/ABI theorem is minted. -/
theorem no_body_violation (literal input depth : Nat) (memory : Mem)
    (inputValid : input < modulus 64) :
    ¬ BodyViolation (module literal) (initial literal input depth memory) := by
  exact returned_excludes_body_violation (module literal)
    (initial literal input depth memory) 3
    [.int .u64 ((input + literal) % modulus 64)]
    (run_exact literal input depth memory inputValid)

theorem original_no_body_violation (input depth : Nat) (initialState : Core)
    (inputValid : input < modulus 64)
    (started : start (module 7) 0 [.int .u64 input] depth = .ok initialState) :
    ¬ BodyViolation (module 7) initialState := by
  rw [start_exact 7 input depth inputValid] at started
  cases started
  exact no_body_violation 7 input depth Mem.empty inputValid

/-- The canonical operator correspondence is reused, not a second arithmetic
    evaluator or a model equation admitted as an axiom. -/
theorem minirust_add (fuel : Nat) (machine : MR_Machine) (input : Nat)
    (inputValid : input < modulus 64) :
    MRf.Machine.eval_bin_op (fuel + 4) machine (.Int .Add)
      (.Int (readAt false 64 input), .Int (mrIntTy false .u64))
      (.Int (readAt false 64 7), .Int (mrIntTy false .u64)) =
      SOut.ok (SRes.ok (.Int (readAt false 64 ((input + 7) % modulus 64)),
        .Int (mrIntTy false .u64))) :=
  add_minirust fuel machine false .u64 input 7 inputValid (by decide)

end SemRU64Addition

