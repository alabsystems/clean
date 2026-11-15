prelude
import ReplayHonestSortDefBase

/-!
# `ReplayHonestSortDef` — a family whose sort is an IMPORTED definition

`HSD : HSDSort` is a `Type` family only up to whnf, through `HSDSort` from the base
module, and Lean's kernel checks every declaration below. A re-check that regenerates
`HSD.rec` from the stored family must reduce `HSDSort`, so the definition must be resident
first: `per-constant-verify`'s demand walk once registered the family before it, refused
`HSD.rec` ("Invalid recursor"), and with it every declaration below (decision R147).
-/

inductive HSD : HSDSort
  | mk : Bool → HSD

def hsd_use : HSD := HSD.mk Bool.true

noncomputable def hsd_bit : HSD → Bool := fun h => HSD.rec (motive := fun _ => Bool) (fun b => b) h

theorem hsd_bit_mk : hsd_bit (HSD.mk Bool.true) = Bool.true := rfl
