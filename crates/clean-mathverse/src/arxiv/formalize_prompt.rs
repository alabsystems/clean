// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Prompt constants for the LLM formalization pipeline.
//!
//! Separated from `formalize.rs` to keep file sizes under the 500-line limit.
//! These constants are embedded into the prompt built by
//! [`super::formalize::build_formalization_prompt`].

/// Anti-hallucination guidance with negative examples of fictional Mathlib types.
pub(crate) const ANTI_HALLUCINATION_PROMPT: &str = "\n\
## CRITICAL: Do NOT invent fictional Mathlib types\n\
Many Mathlib types that seem plausible DO NOT EXIST. Common fictional types:\n\
- `CarrierGraph G ℙ V E` — does NOT exist in Mathlib\n\
- `IsCompactRiemannSurface` — invented typeclass, not in Mathlib\n\
- `Divisor X` / `QuotientScheme` / `projectiveSpace k N` — fictional\n\
- `AlgebraicGeometry.Divisors.Basic` — nonexistent import path\n\
- `TopologicalManifold` / `SmoothManifold` — check carefully before using\n\
- `IsHolomorphic` / `MeromorphicFunction` — not standard Mathlib names\n\
- `SchemeOver` / `AffineVariety` / `ProjectiveVariety` — fictional AG types\n\n\
If unsure whether a type exists in Mathlib, define it locally with `sorry`:\n\
```lean\n\
-- Local stub: not available in Mathlib\n\
def RiemannSurface := sorry\n\
def Divisor (X : Type*) := sorry\n\
```\n\n";

/// Known-valid Mathlib types and import paths for LLM reference.
pub(crate) const KNOWN_TYPES_PROMPT: &str = "\
## Known-valid Mathlib types (safe to use)\n\
- `Nat`, `Int`, `Rat`, `Real`, `Complex` (number types)\n\
- `Finset`, `Multiset`, `List`, `Set` (collections)\n\
- `Group`, `CommGroup`, `Ring`, `CommRing`, `Field` (algebra)\n\
- `Module`, `Submodule`, `Ideal`, `Subgroup` (algebraic structures)\n\
- `MonoidHom`, `RingHom`, `AlgHom`, `MulEquiv` (morphisms)\n\
- `TopologicalSpace`, `MetricSpace`, `NormedSpace` (topology/analysis)\n\
- `IsOpen`, `IsClosed`, `IsCompact`, `IsConnected` (predicates)\n\
- `Continuous`, `Differentiable`, `MeasureTheory.Integrable` (analysis)\n\
- `Filter.Tendsto`, `Filter.Eventually` (filters/limits)\n\
- `SimpleGraph`, `Fintype`, `Infinite` (combinatorics/finiteness)\n\
- `Nat.Prime`, `Polynomial`, `MvPolynomial` (number theory/algebra)\n\
- `Matrix`, `LinearMap`, `BilinForm` (linear algebra)\n\
- `T2Space`, `CompactSpace`, `NormalSpace` (topology)\n\n\
## Known-valid import paths\n\
- `import Mathlib.Data.Nat.Basic` / `import Mathlib.Data.Real.Basic`\n\
- `import Mathlib.Algebra.Group.Basic` / `import Mathlib.Topology.Basic`\n\
- `import Mathlib.Analysis.NormedSpace.Basic` / `import Mathlib.Tactic`\n\n";

/// Lean 4 Init types/tactics that are always available (no Mathlib import needed).
pub(crate) const LEAN4_INIT_TYPES_PROMPT: &str = "\
## Available Lean 4 Init types (always available, no import needed)\n\
### Core types\n\
- `Nat`, `Int`, `Bool`, `String`, `Char`, `Float`, `UInt8`..`UInt64`\n\
- `Prop`, `True`, `False`, `Unit`, `Empty`, `Option`, `Except`\n\
- `List`, `Array`, `Fin`, `Prod`, `Sum`, `Sigma`, `Subtype`\n\n\
### Core propositions & type classes\n\
- `Eq`, `Ne`, `HEq`, `And`, `Or`, `Not`, `Iff`, `Exists`\n\
- `LE`, `LT`, `BEq`, `Ord`, `Hashable`, `Repr`, `ToString`\n\
- `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Pow`, `Neg`, `HPow`\n\
- `Decidable`, `DecidableEq`, `Inhabited`, `Nonempty`\n\n\
### Available tactics (from Init.Tactics)\n\
- `rfl`, `trivial`, `exact`, `apply`, `intro`, `intros`, `assumption`\n\
- `cases`, `induction`, `match`, `simp`, `mathverse`, `decide`\n\
- `constructor`, `left`, `right`, `exists`, `have`, `let`, `show`\n\
- `rw`, `rewrite`, `calc`, `suffices`, `by_contra`, `exfalso`\n\
- `congr`, `funext`, `ext`, `ring`, `linarith` (need `import Mathlib.Tactic`)\n\n";

/// Common LLM failure patterns and how to fix them.
pub(crate) const FAILURE_PATTERNS_PROMPT: &str = "\
## Common failure patterns to AVOID\n\n\
### Incomplete let bindings\n\
BAD:  `let x := foo`        (missing body after let)\n\
GOOD: `let x := foo; bar x` (let must have a continuation)\n\
GOOD: `let x := foo\n  bar x` (newline + indent also works)\n\n\
### Missing binders\n\
BAD:  `theorem foo : n + 0 = n`    (what is `n`?)\n\
GOOD: `theorem foo (n : Nat) : n + 0 = n`\n\n\
### Dot notation on auto-implicit types\n\
BAD:  `G.Adj u v`           (G has no namespace, `.Adj` fails)\n\
GOOD: `SimpleGraph.Adj G u v`\n\
BAD:  `T.IsTree`            (dot notation on variable)\n\
GOOD: `IsTree T`             (use as predicate/typeclass)\n\n\
### Fictional Mathlib types disguised as real ones\n\
BAD:  `import Mathlib.Topology.Manifold.SmoothManifold`\n\
GOOD: `def SmoothManifold := sorry  -- not in Init or known Mathlib`\n\n\
### Using `by` without a tactic\n\
BAD:  `theorem foo : P := by`  (incomplete tactic block)\n\
GOOD: `theorem foo : P := by sorry`\n\n";

/// Formalization rules including anti-fictional-import directives.
pub(crate) const RULES_PROMPT: &str = "\
## Rules\n\
1. Output ONLY the Lean 4 code, no explanations\n\
2. Use ONLY types from Lean 4 Init or the known-valid Mathlib list above\n\
3. For definitions: use `def` or `structure` or `class`\n\
4. For theorems: use `theorem` with the full type signature\n\
5. ALWAYS bind free variables explicitly: `(n : Nat)`, `(G : SimpleGraph V)`\n\
6. If a concept has no known Lean 4 / Mathlib equivalent, define it locally with `sorry`\n\
7. Preserve the mathematical meaning exactly — do not simplify or approximate\n\
8. Use universe-polymorphic types where appropriate\n\
9. Do NOT import Mathlib modules you are not certain exist\n\
10. When in doubt, use `sorry`-based local definitions over fictional imports\n\
11. Every `let` binding MUST have a body expression after it\n\
12. Use explicit function application (`f x y`) not dot notation on variables\n\n\
## Output (Lean 4 code only)\n```lean\n";
