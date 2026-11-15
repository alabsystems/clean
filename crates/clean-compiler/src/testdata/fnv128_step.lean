-- Exact executable definitions from trust-cg proofs/sentinel_decide_spec.lean.
-- Source translation fixture; no collision-resistance or full hash proof claim.
def trust_cg_fnv128_step_lo (lo byte : UInt64) : UInt64 :=
  (lo ^^^ byte) * 315

def trust_cg_fnv128_step_hi (hi lo byte : UInt64) : UInt64 :=
  let mixed := lo ^^^ byte
  let lowProduct := (mixed &&& 4294967295) * 315
  let highProduct := (mixed >>> 32) * 315 + (lowProduct >>> 32)
  hi * 315 + (mixed <<< 24) + (highProduct >>> 32)
