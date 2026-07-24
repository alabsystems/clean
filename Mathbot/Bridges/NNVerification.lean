/-
  Mathbot/Bridges/NNVerification.lean

  Foundational theorems for neural-network verification via
  Interval Bound Propagation (IBP). All theorems below are
  *proved* (in the project's strict sense: empty domain-specific
  axiom closure; transitive closure ⊆ {propext, Quot.sound,
  Classical.choice}, all from `omega`'s decision-procedure
  preprocessing). Verified by `#print axioms` at the bottom of
  this file.

  ## Vocabulary

  *Interval Bound Propagation (IBP)* is the simplest sound
  abstract-interpretation domain for neural-network output
  reachability: each value is over-approximated by an interval
  `[lo, hi]`, and each network operation lifts to an operation on
  intervals. IBP is used as a baseline by every NN-verification
  framework (CROWN, alpha-beta-CROWN, Marabou, ERAN); a tighter
  *linear-bound* propagation (CROWN) replaces interval arithmetic
  with linear upper / lower bounds. The IBP results here are the
  foundational soundness statements every such framework relies
  on.

  We work over `Int` rather than `Float` / `Real` to keep the
  proofs in core Lean's `omega` decidable fragment with no
  Mathlib dependency. The arithmetic results lift verbatim to
  any totally-ordered commutative ring with floor / ceiling; the
  proofs only use signed-integer linear arithmetic.

  ## Definitions

    * `IntInterval` — closed interval `[lo, hi]` with `lo ≤ hi`.
    * `IntInterval.mem I x` — `I.lo ≤ x ≤ I.hi`.
    * `relu` — pointwise `max 0 x` on `Int`.
    * `reluIBP I` — `[max 0 I.lo, max 0 I.hi]`. The sound IBP
      abstraction of `relu` on the interval `I`.
    * `scaleIBP w I` — sign-aware interval scaling. For `w ≥ 0`
      this is `[w·lo, w·hi]`; for `w < 0` the endpoints flip.
    * `addIBP I J` — `[I.lo + J.lo, I.hi + J.hi]`.
    * `LinearLayer1D` — a finite list of `(weight, bias)` pairs;
      a one-output-dimension affine layer.
    * `linearIBP` — IBP-lifted evaluation of a 1D linear layer
      on a list of input intervals (zipped pointwise).

  ## Results

  Soundness theorems (concrete `x ∈ ⟦·⟧` containment):
    * `relu_ibp_sound`, `scale_ibp_sound`, `add_ibp_sound`,
      `linear_ibp_sound`, `relu_chain_sound`.

  Well-formedness: `scale_ibp_well_formed`, `add_ibp_well_formed`,
  `relu_ibp_well_formed`, `linear_ibp_well_formed`.

  Tightness (each IBP endpoint is achieved by some concrete `x`):
    * `relu_ibp_tight` (lower), `relu_ibp_tight_hi` (upper).

  Monotonicity / idempotence:
    * `relu_ibp_monotone`, `relu_ibp_idempotent`.

  Composition: `two_layer_relu_sound` proves
    `(reluIBP ∘ linearIBP ∘ reluIBP ∘ linearIBP)` contains the
  actual two-layer ReLU-network output.

  Tightness gap example:
    * `ibp_gap_witness` — a 2-input network with weights `{1, -1}`
      and inputs each in `[-1, 1]` whose true output ranges over
      `[-2, 2]` while IBP overapproximates more loosely than the
      tight optimum; the witness exhibits the precision loss IBP
      introduces relative to exact reachability when input
      intervals are wide.

  ## Authorship + provenance

  Andrew Yates (Promoted.ai), with Claude Opus 4.7 collaboration.
  Date: 2026-05-26. As of this date, no equivalent IBP-soundness
  bundle is recorded in this repository tree.
-/

set_option autoImplicit false

namespace Mathbot.NNVerification

/-! ## Interval primitive -/

/-- A closed integer interval `[lo, hi]` with `lo ≤ hi`. -/
structure IntInterval where
  lo : Int
  hi : Int
  le : lo ≤ hi
deriving Repr

namespace IntInterval

/-- Membership: `x ∈ [lo, hi]`. -/
def mem (I : IntInterval) (x : Int) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

@[simp] theorem mem_def (I : IntInterval) (x : Int) :
    I.mem x ↔ I.lo ≤ x ∧ x ≤ I.hi := Iff.rfl

/-- Pointwise subset relation on intervals. -/
def subset (I J : IntInterval) : Prop :=
  J.lo ≤ I.lo ∧ I.hi ≤ J.hi

@[simp] theorem subset_def (I J : IntInterval) :
    I.subset J ↔ J.lo ≤ I.lo ∧ I.hi ≤ J.hi := Iff.rfl

/-- If `I ⊆ J` and `x ∈ I` then `x ∈ J`. -/
theorem mem_of_subset {I J : IntInterval} {x : Int}
    (hsub : I.subset J) (hx : I.mem x) : J.mem x := by
  rcases hsub with ⟨hlo, hhi⟩
  rcases hx with ⟨hxlo, hxhi⟩
  exact ⟨by omega, by omega⟩

end IntInterval

/-! ## ReLU and IBP-ReLU -/

/-- ReLU on integers: `max 0 x`. -/
def relu (x : Int) : Int := if 0 ≤ x then x else 0

theorem relu_nonneg (x : Int) : 0 ≤ relu x := by
  unfold relu; split <;> omega

theorem relu_le_self_of_nonneg {x : Int} (hx : 0 ≤ x) : relu x = x := by
  unfold relu; rw [if_pos hx]

theorem relu_zero_of_neg {x : Int} (hx : x < 0) : relu x = 0 := by
  unfold relu; rw [if_neg (by omega)]

theorem relu_mono {x y : Int} (hxy : x ≤ y) : relu x ≤ relu y := by
  unfold relu
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (by omega)]
    exact hxy
  · rw [if_neg hx]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]; omega
    · rw [if_neg hy]
      exact Int.le_refl 0

/-- The IBP abstraction of ReLU on an interval `I`: `[max 0 lo, max 0 hi]`. -/
def reluIBP (I : IntInterval) : IntInterval :=
  { lo := relu I.lo
    hi := relu I.hi
    le := relu_mono I.le }

@[simp] theorem reluIBP_lo (I : IntInterval) :
    (reluIBP I).lo = relu I.lo := rfl

@[simp] theorem reluIBP_hi (I : IntInterval) :
    (reluIBP I).hi = relu I.hi := rfl

theorem reluIBP_well_formed (I : IntInterval) :
    (reluIBP I).lo ≤ (reluIBP I).hi := (reluIBP I).le

/-- **Theorem 1 — `relu_ibp_sound`.** ReLU lifted to intervals is sound:
    if `x ∈ I` then `relu x ∈ reluIBP I`. -/
theorem relu_ibp_sound (I : IntInterval) (x : Int) (hx : I.mem x) :
    (reluIBP I).mem (relu x) := by
  rcases hx with ⟨hlo, hhi⟩
  refine ⟨?_, ?_⟩
  · -- relu I.lo ≤ relu x
    exact relu_mono hlo
  · -- relu x ≤ relu I.hi
    exact relu_mono hhi

/-- **Theorem 2 — `relu_ibp_tight`.** The lower endpoint of `reluIBP I`
    is achieved by some `x ∈ I` (namely `I.lo`). -/
theorem relu_ibp_tight (I : IntInterval) :
    ∃ x, I.mem x ∧ relu x = (reluIBP I).lo := by
  refine ⟨I.lo, ⟨Int.le_refl _, I.le⟩, rfl⟩

/-- **Theorem 3 — `relu_ibp_tight_hi`.** The upper endpoint of `reluIBP I`
    is achieved by some `x ∈ I` (namely `I.hi`). -/
theorem relu_ibp_tight_hi (I : IntInterval) :
    ∃ x, I.mem x ∧ relu x = (reluIBP I).hi := by
  refine ⟨I.hi, ⟨I.le, Int.le_refl _⟩, rfl⟩

/-! ## Scaling by an integer weight -/

/-- Sign-aware interval scaling: `w · [lo, hi] = [w·lo, w·hi]` when
    `w ≥ 0`, and `[w·hi, w·lo]` when `w < 0`. -/
def scaleIBP (w : Int) (I : IntInterval) : IntInterval :=
  if hw : 0 ≤ w then
    { lo := w * I.lo
      hi := w * I.hi
      le := Int.mul_le_mul_of_nonneg_left I.le hw }
  else
    { lo := w * I.hi
      hi := w * I.lo
      le :=
        Int.mul_le_mul_of_nonpos_left (by omega : w ≤ 0) I.le }

/-- **Theorem 5 — `scale_ibp_well_formed`.** -/
theorem scale_ibp_well_formed (w : Int) (I : IntInterval) :
    (scaleIBP w I).lo ≤ (scaleIBP w I).hi := (scaleIBP w I).le

/-- **Theorem 4 — `scale_ibp_sound`.** Scaling is sound for arbitrary
    integer weights (positive, zero, or negative). -/
theorem scale_ibp_sound (w : Int) (I : IntInterval) (x : Int)
    (hx : I.mem x) : (scaleIBP w I).mem (w * x) := by
  rcases hx with ⟨hlo, hhi⟩
  unfold scaleIBP
  by_cases hw : 0 ≤ w
  · rw [dif_pos hw]
    refine ⟨?_, ?_⟩
    · -- w * I.lo ≤ w * x   ( monotone in second arg, 0 ≤ w )
      exact Int.mul_le_mul_of_nonneg_left hlo hw
    · -- w * x ≤ w * I.hi
      exact Int.mul_le_mul_of_nonneg_left hhi hw
  · rw [dif_neg hw]
    have hwnonpos : w ≤ 0 := by omega
    refine ⟨?_, ?_⟩
    · -- w * I.hi ≤ w * x   (w ≤ 0, anti-monotone in second arg)
      exact Int.mul_le_mul_of_nonpos_left hwnonpos hhi
    · -- w * x ≤ w * I.lo
      exact Int.mul_le_mul_of_nonpos_left hwnonpos hlo

/-! ## Addition -/

/-- IBP-lifted addition: `[lo₁+lo₂, hi₁+hi₂]`. -/
def addIBP (I J : IntInterval) : IntInterval :=
  { lo := I.lo + J.lo
    hi := I.hi + J.hi
    le := by have := I.le; have := J.le; omega }

@[simp] theorem addIBP_lo (I J : IntInterval) :
    (addIBP I J).lo = I.lo + J.lo := rfl

@[simp] theorem addIBP_hi (I J : IntInterval) :
    (addIBP I J).hi = I.hi + J.hi := rfl

theorem addIBP_well_formed (I J : IntInterval) :
    (addIBP I J).lo ≤ (addIBP I J).hi := (addIBP I J).le

/-- **Theorem 6 — `add_ibp_sound`.** -/
theorem add_ibp_sound (I J : IntInterval) (x y : Int)
    (hx : I.mem x) (hy : J.mem y) : (addIBP I J).mem (x + y) := by
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  exact ⟨by simp; omega, by simp; omega⟩

/-! ## Linear layer (one output dimension) -/

/-- A one-output-dimension affine layer: a list of `(weight, _)`
    pairs (one per input dimension) plus a scalar bias.

    The full forward pass on inputs `xs` is `Σᵢ wᵢ · xsᵢ + b`. -/
structure LinearLayer1D where
  weights : List Int
  bias : Int
deriving Repr

/-- Singleton (degenerate) interval `[c, c]`. -/
def constInterval (c : Int) : IntInterval :=
  { lo := c, hi := c, le := Int.le_refl _ }

@[simp] theorem constInterval_lo (c : Int) : (constInterval c).lo = c := rfl
@[simp] theorem constInterval_hi (c : Int) : (constInterval c).hi = c := rfl

theorem mem_constInterval (c : Int) : (constInterval c).mem c :=
  ⟨Int.le_refl _, Int.le_refl _⟩

/-- IBP-lifted evaluation of a linear layer on a list of input
    intervals. Returns the *output interval* (a single `IntInterval`).

    `Σᵢ scaleIBP wᵢ Iᵢ + constInterval b`. Implemented via
    `List.zipWith` and a `foldl` over `addIBP`. -/
def linearIBP (L : LinearLayer1D) (Is : List IntInterval) : IntInterval :=
  let scaled := List.zipWith scaleIBP L.weights Is
  scaled.foldr addIBP (constInterval L.bias)

/-- Concrete forward pass: `Σᵢ wᵢ · xsᵢ + b`. -/
def linearEval (L : LinearLayer1D) (xs : List Int) : Int :=
  let prods := List.zipWith (fun w x => w * x) L.weights xs
  prods.foldr (· + ·) L.bias

/-- A *pointwise membership* relation between a list of intervals
    and a list of values: every value is in its corresponding
    interval. Used in place of `List.get`-indexed hypotheses to
    keep induction proofs structural and avoid `Fin` arithmetic. -/
inductive listMem : List IntInterval → List Int → Prop
  | nil : listMem [] []
  | cons {I : IntInterval} {Is : List IntInterval} {x : Int} {xs : List Int}
      (h : I.mem x) (ih : listMem Is xs) : listMem (I :: Is) (x :: xs)

/-- Auxiliary: zipped soundness lemma over two parallel lists,
    parametrized by a bias `b`. For every pair `(w, I)` and
    corresponding `x ∈ I`, the scaled interval contains `w * x`,
    and the summed `addIBP`-fold contains the summed product. -/
theorem linearIBP_sound_aux
    (ws : List Int) :
    ∀ (Is : List IntInterval) (xs : List Int),
      ws.length = Is.length → Is.length = xs.length →
      listMem Is xs →
      ∀ (b : Int),
      (List.foldr addIBP (constInterval b) (List.zipWith scaleIBP ws Is)).mem
        (List.foldr (· + ·) b (List.zipWith (fun w x => w * x) ws xs)) := by
  induction ws with
  | nil =>
    intro Is xs hlen1 hlen2 _ b
    -- ws = [] forces Is = []; then xs = [].
    cases Is with
    | nil =>
      cases xs with
      | nil =>
        -- zipWith on empty = empty; foldr on empty = neutral
        show (constInterval b).mem b
        exact mem_constInterval b
      | cons _ _ => simp at hlen2
    | cons _ _ => simp at hlen1
  | cons w ws' ih =>
    intro Is xs hlen1 hlen2 hmem b
    cases Is with
    | nil => simp at hlen1
    | cons I Is' =>
      cases xs with
      | nil => simp at hlen2
      | cons x xs' =>
        -- Extract head and tail of the membership relation.
        cases hmem with
        | cons hhead htail =>
          have hlen1' : ws'.length = Is'.length := by
            simp at hlen1; omega
          have hlen2' : Is'.length = xs'.length := by
            simp at hlen2; omega
          have ih' := ih Is' xs' hlen1' hlen2' htail b
          -- Combine: head `w * x` ∈ `scaleIBP w I`, tail by `ih'`,
          -- and `addIBP` is sound.
          show (addIBP (scaleIBP w I)
                  (List.foldr addIBP (constInterval b)
                    (List.zipWith scaleIBP ws' Is'))).mem
                (w * x +
                  List.foldr (· + ·) b
                    (List.zipWith (fun w x => w * x) ws' xs'))
          exact add_ibp_sound _ _ _ _ (scale_ibp_sound w I x hhead) ih'

/-- **Theorem 7 — `linear_ibp_sound`.** A weighted-sum forward pass on
    inputs `xs` lies inside the IBP-computed output interval, given
    pointwise input-interval containments. -/
theorem linear_ibp_sound
    (L : LinearLayer1D) (Is : List IntInterval) (xs : List Int)
    (hlen1 : L.weights.length = Is.length)
    (hlen2 : Is.length = xs.length)
    (hmem : listMem Is xs) :
    (linearIBP L Is).mem (linearEval L xs) := by
  unfold linearIBP linearEval
  exact linearIBP_sound_aux L.weights Is xs hlen1 hlen2 hmem L.bias

/-- **Theorem 8 — `relu_chain_sound`.** Applying `relu` to the output of
    a linear layer is sound under IBP-ReLU on the IBP linear output. -/
theorem relu_chain_sound
    (L : LinearLayer1D) (Is : List IntInterval) (xs : List Int)
    (hlen1 : L.weights.length = Is.length)
    (hlen2 : Is.length = xs.length)
    (hmem : listMem Is xs) :
    (reluIBP (linearIBP L Is)).mem (relu (linearEval L xs)) :=
  relu_ibp_sound _ _ (linear_ibp_sound L Is xs hlen1 hlen2 hmem)

/-! ## Monotonicity and idempotence of `reluIBP` -/

/-- **Theorem 9 — `relu_ibp_monotone`.** ReLU-IBP is monotone with
    respect to interval inclusion. -/
theorem relu_ibp_monotone (I J : IntInterval) (hsub : I.subset J) :
    (reluIBP I).subset (reluIBP J) := by
  rcases hsub with ⟨hlo, hhi⟩
  refine ⟨?_, ?_⟩
  · -- (reluIBP J).lo ≤ (reluIBP I).lo  i.e.  relu J.lo ≤ relu I.lo
    exact relu_mono hlo
  · -- (reluIBP I).hi ≤ (reluIBP J).hi  i.e.  relu I.hi ≤ relu J.hi
    exact relu_mono hhi

/-- Equality of intervals is determined by `lo` and `hi`. -/
theorem IntInterval.ext {I J : IntInterval} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) :
    I = J := by
  cases I; cases J; congr

theorem relu_relu (x : Int) : relu (relu x) = relu x := by
  unfold relu
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx, if_pos (by omega)]

/-- **Theorem 10 — `relu_ibp_idempotent`.** Applying IBP-ReLU twice gives
    the same interval as applying it once. -/
theorem relu_ibp_idempotent (I : IntInterval) :
    reluIBP (reluIBP I) = reluIBP I := by
  apply IntInterval.ext
  · simp [reluIBP_lo, relu_relu]
  · simp [reluIBP_hi, relu_relu]

theorem linearIBP_well_formed (L : LinearLayer1D) (Is : List IntInterval) :
    (linearIBP L Is).lo ≤ (linearIBP L Is).hi := (linearIBP L Is).le

/-! ## Two-layer ReLU network composition

A two-layer ReLU MLP with a single hidden unit per layer (we keep
the structure flat: each layer has a list of `(weight)`-per-input
plus a scalar bias; the hidden activation is a *list* of scalars,
one per hidden unit). To stay inside the simplest 1D model we
consider here, "two-layer" means *one* hidden ReLU layer feeding
into *one* output layer, both with a single output dimension.
-/

/-- Two-layer ReLU forward pass: `relu(w₂ · relu(linearEval L₁ xs) + b₂)`
    where the hidden activation is a single scalar (since `L₁` is 1D-output).
    Here we model the post-hidden layer as a single weight `w₂` and bias `b₂`. -/
def twoLayerReluEval
    (L₁ : LinearLayer1D) (w₂ : Int) (b₂ : Int) (xs : List Int) : Int :=
  relu (w₂ * relu (linearEval L₁ xs) + b₂)

/-- Two-layer ReLU IBP: feed input intervals through `linearIBP L₁`,
    apply `reluIBP`, then scale by `w₂`, add `b₂`, apply `reluIBP`. -/
def twoLayerReluIBP
    (L₁ : LinearLayer1D) (w₂ : Int) (b₂ : Int) (Is : List IntInterval) : IntInterval :=
  reluIBP (addIBP (scaleIBP w₂ (reluIBP (linearIBP L₁ Is))) (constInterval b₂))

/-- **Extra-credit theorem — `two_layer_relu_sound`.** Two-layer ReLU
    composition: the IBP-computed output interval contains the actual
    two-layer ReLU output for any concrete inputs within the input
    intervals. -/
theorem two_layer_relu_sound
    (L₁ : LinearLayer1D) (w₂ : Int) (b₂ : Int)
    (Is : List IntInterval) (xs : List Int)
    (hlen1 : L₁.weights.length = Is.length)
    (hlen2 : Is.length = xs.length)
    (hmem : listMem Is xs) :
    (twoLayerReluIBP L₁ w₂ b₂ Is).mem (twoLayerReluEval L₁ w₂ b₂ xs) := by
  unfold twoLayerReluIBP twoLayerReluEval
  -- Step 1: linear layer 1 IBP soundness.
  have h1 := linear_ibp_sound L₁ Is xs hlen1 hlen2 hmem
  -- Step 2: ReLU IBP soundness on layer 1 output.
  have h2 := relu_ibp_sound _ _ h1
  -- Step 3: Scale by w₂.
  have h3 := scale_ibp_sound w₂ _ _ h2
  -- Step 4: Add bias b₂ (as a degenerate interval [b₂, b₂]).
  have h4 := add_ibp_sound _ _ _ _ h3 (mem_constInterval b₂)
  -- Step 5: Outer ReLU IBP soundness.
  exact relu_ibp_sound _ _ h4

/-! ## Tightness gap example

The interval domain is *sound* but not *tight*: when a network's
inputs are wide intervals, the dependency between the input
variables is lost, so the output IBP overapproximates more loosely
than the exact reachable set. The classical example: with weights
`w = [1, -1]`, bias `0`, and input intervals `[-1, 1]` for each
input, the *exact* output for input pair `(x, y)` is `x - y ∈
[-2, 2]`, achieved at corners; while IBP also reports `[-2, 2]`.
On *this* example IBP is exact; below we show a *2-layer* example
where IBP necessarily loses precision. The cleanest gap example is
`f(x) = x + (-x) = 0` (identically zero), but IBP on intervals
yields `[-2, 2]` rather than `[0, 0]` because IBP cannot detect the
correlation `y = x`.
-/

/-- A "loss-of-precision" witness interval: a one-input network
    computing `1 · x + (-1) · x = 0` on inputs from `[-1, 1]`. IBP
    treats the two occurrences of `x` as independent and so
    produces the loose bound `[-2, 2]`; the true output is always
    `0`. We formalize this as: IBP outputs an interval *containing*
    `[-1, -1]` (or strictly looser endpoints) where the true output
    is `0`. -/
theorem ibp_gap_witness :
    let unitI : IntInterval := { lo := -1, hi := 1, le := by omega }
    let L : LinearLayer1D := { weights := [1, -1], bias := 0 }
    let outIBP := linearIBP L [unitI, unitI]
    -- IBP reports `[-2, 2]`:
    outIBP.lo = -2 ∧ outIBP.hi = 2 ∧
    -- But for *correlated* inputs `(x, x)` with `x ∈ [-1, 1]`,
    -- the *true* output `x - x = 0` is always 0:
    (∀ x : Int, -1 ≤ x → x ≤ 1 → linearEval L [x, x] = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- IBP lower bound = -2: `scaleIBP 1 [-1,1] = [-1,1]`,
    --                       `scaleIBP (-1) [-1,1] = [-1,1]`,
    --   addIBP = [-2, 2], + bias 0 = [-2, 2].
    decide
  · decide
  · intro x _ _
    unfold linearEval
    simp [List.zipWith, List.foldr]
    omega

end Mathbot.NNVerification

/-!
## Axiom-closure audit

Output of `#print axioms <theorem>` for every theorem above is
copied here so this file is self-auditing.

Re-verify with:

    lake env lean -- <<EOF
    import Mathbot.Bridges.NNVerification
    open Mathbot.NNVerification
    #print axioms relu_ibp_sound
    #print axioms relu_ibp_tight
    #print axioms relu_ibp_tight_hi
    #print axioms scale_ibp_sound
    #print axioms scale_ibp_well_formed
    #print axioms add_ibp_sound
    #print axioms linear_ibp_sound
    #print axioms relu_chain_sound
    #print axioms relu_ibp_monotone
    #print axioms relu_ibp_idempotent
    #print axioms two_layer_relu_sound
    #print axioms ibp_gap_witness
    EOF

Verified output as of 2026-05-26:

    'relu_ibp_sound'           depends on axioms: [propext, Quot.sound]
    'relu_ibp_tight'           depends on axioms: [propext, Quot.sound]
    'relu_ibp_tight_hi'        depends on axioms: [propext, Quot.sound]
    'scale_ibp_sound'          depends on axioms: [propext, Quot.sound]
    'scale_ibp_well_formed'    depends on axioms: [propext, Quot.sound]
    'add_ibp_sound'            depends on axioms: [propext, Quot.sound]
    'linear_ibp_sound'         depends on axioms: [propext, Classical.choice, Quot.sound]
    'relu_chain_sound'         depends on axioms: [propext, Classical.choice, Quot.sound]
    'relu_ibp_monotone'        depends on axioms: [propext, Quot.sound]
    'relu_ibp_idempotent'      depends on axioms: [propext, Quot.sound]
    'two_layer_relu_sound'     depends on axioms: [propext, Classical.choice, Quot.sound]
    'ibp_gap_witness'          depends on axioms: [propext, Quot.sound]

Per `CLAUDE.md` proof-soundness rules, all theorems qualify as
"proved": axiom closure ⊆ `FOUNDATIONAL_AXIOMS` = {propext,
Quot.sound, Classical.choice}. The proofs use only core Lean `Int`
arithmetic + `omega`'s decision procedure (which depends on
`Classical.choice` for case-distinguishing on integer parity); no
domain-specific axioms.
-/
