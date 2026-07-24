# TLAPS Integration Benchmarks

Benchmark suite for testing `clean-tla`'s ability to prove TLA+ proof obligations.

## Structure

```
benchmarks/tlaps/
├── nat_induction/     # Natural number induction proofs
├── wf_induction/      # Well-founded induction proofs
├── lex_induction/     # Lexicographic induction proofs
├── leads_to/          # Progress measure / leads-to proofs
├── temporal/          # Temporal logic proofs
└── auto/              # Simplification / propositional proofs
```

## Obligation Format

Each JSON file represents a single proof obligation. See `designs/2026-01-16-tlaps-benchmark-schema.md` for the full schema specification.

### Example

```json
{
  "id": "nat_induction/sum_formula",
  "module": "SumFormulaTest",
  "hypotheses": [...],
  "goal": {"forall_in": ["n", "Nat", ...]},
  "tactic_hint": "induction",
  "expected_result": true,
  "difficulty": "easy",
  "tags": ["nat_induction", "arithmetic"]
}
```

## Running Benchmarks

```bash
# From Clean root
clean tlaps bench benchmarks/tlaps/

# Run specific category
clean tlaps bench benchmarks/tlaps/nat_induction/

# Run single obligation
clean tlaps bench benchmarks/tlaps/nat_induction/sum_formula.json
```

## Adding Benchmarks

1. Create a new JSON file in the appropriate category directory
2. Follow the schema from `designs/2026-01-16-tlaps-benchmark-schema.md`
3. Run the benchmark to verify it parses correctly
4. Update this README if adding a new category

## Success Targets

| Category | Target | Current (50 tests) | Notes |
|----------|--------|-------------------|-------|
| nat_induction | 80% | 94.4% (17/18) | **TARGET MET** via ring tactic + nested forall ([W]214, [R]91) |
| wf_induction | 60% | 0% (0/1) | Needs WF induction schema |
| lex_induction | 60% | 0% (0/1) | Needs hypothesis specialization |
| leads_to | 50% | 100.0% (5/5) | **TARGET MET** via transitivity/disjunction ([W]215) |
| temporal | 50% | 100.0% (4/4) | **TARGET MET** |
| auto | 90% | 90.5% (19/21) | **TARGET MET** (2 are negative tests) |

**Overall**: 90% success rate (45/50 proved), 94% correctness rate (47/50)

### What Works
- Simple nat_induction: `sum_formula`, `factorial_positive`, `trivial_forall`
- Basic arithmetic: `add_zero`, `zero_add`, `mul_zero`
- Nested quantifiers: `add_comm`, `succ_add` (after [R]91 nested forall fix)
- Simple propositional: `modus_ponens`, `disjunction_{left,right}`
- Biconditionals: `contrapositive`, `modus_tollens` (after [P]72 init fix)
- Commutativity: `and_comm`, `or_comm`
- De Morgan: `de_morgan_or`
- Classical: `double_negation_elim`, `double_negation_intro`, `de_morgan_and` (after by_cases fix)
- Conjunction: `conjunction_intro`, `conjunction_elim_{left,right}` (after [W]207 BVar fix)
- Trivial temporal: `always_true`, `eventually_true`
- Temporal reasoning: `always_implies_eventually`, `always_intro` ([W]211, [W]212)
- Progress measure: `leads_to/reflexive`, `counter_to_max`
- Closed-form formulas: `double_formula` (after [W]213 distributivity)

### Fixed: Ring Tactic (#66)

**[W]214**: Implemented polynomial normalization for algebraic equality proofs per R96 design.

Ring tactic approach:
- Convert expressions to canonical sum-of-monomials form
- Sort monomials by degree then lexicographically
- Compare normalized forms for structural equality

This fixed: `triangular_number`, `sum_squares`

nat_induction improved from 77.8% → 88.9% (14/18 → 16/18).

### Known Gaps (3 remaining)
- **2-arg recursive definitions**: `power_positive` - needs hypothesis specialization (n=2)
- **Well-founded induction**: `gcd_terminates` - needs WF induction schema with measure extraction
- **Lexicographic**: `ackermann_base` - needs hypothesis specialization for operator application

**Root cause:** All 3 failures share the same blocker - universally quantified hypotheses are not specialized.
See `reports/research/2026-01-16-researcher-101-hypothesis-specialization-guide.md` for implementation details.

### Fixed: add_assoc (Triple-nested quantifiers)

**[R]91 nested forall handling**: The recursive nested induction approach now handles 3-variable cases.
nat_induction improved from 88.9% → 94.4% (16/18 → 17/18).

### Fixed: leads_to Rules (#59)

**[W]215**: Implemented transitivity and disjunction inference rules per R99 implementation guide.

leads_to improved from 60% → 100% (3/5 → 5/5).

### Fixed: Environment Initialization (#67)

**[P]72**: TlaTacticEngine::new() now calls env.init_iff(), env.init_and(), etc.

This fixed 7 auto benchmarks:
- `contrapositive`, `modus_tollens`, `de_morgan_or`
- `and_comm`, `or_comm`
- `conjunction_elim_left`, `conjunction_elim_right`

### Fixed: BVar Lifting (#67)

**[W]207**: Fixed de Bruijn index mismatch in hypothesis type encoding.

When wrapping obligations with hypothesis Pi-types, each hypothesis type
was computed at depth len(prop_vars) but used at increasing depths as inner
hypotheses are wrapped. The fix lifts each hypothesis type by (num_hyps - 1 - i).

This fixed: `conjunction_intro` (h_p: P, h_q: Q ⊢ P ∧ Q)

### Fixed: Classical by_cases (#67)

**[W]209**: Implemented `try_by_cases_for_disjunction` in tauto.rs.

For de_morgan_and (`¬(P ∧ Q) → ¬P ∨ ¬Q`):
- Case analysis on P using Classical.em
- Case ¬P: prove via `left` → `assumption`
- Case P: prove `¬Q` via contradiction (have A∧B → False with h)

This completed the auto category at 90.5% (19/21) with 100% correctness.

### Fixed: Nested Forall Handling (#59)

**[R]91**: Added `try_prove_nested_goal` and `try_nested_forall_step_case` in tactic.rs.

For nested quantifiers like `∀n ∈ Nat: ∀m ∈ Nat: n + m = m + n`:
- Base case handler recursively applies induction to inner foralls
- Step case uses `check_shifted_equality` to verify equality preservation under n → n+1
- Handles commutativity and associativity-style proofs

This fixed: `add_comm`, `succ_add` (nested quantifier proofs)

### Fixed: Temporal Reasoning (#59)

**[W]211**: Added `try_eventually_from_always` for proving ◇P from □P.

The inference rule: If □P holds, then P holds in the current state, therefore ◇P holds.
This fixed: `always_implies_eventually`

**[W]212**: Added `try_always_via_stability` for proving □P from stability pattern.

The stability pattern:
- Hypothesis P (initial condition)
- Hypothesis □(P → □P) (stability: once true, always true)
- Conclusion: □P by coinduction

This fixed: `always_intro`

Together these advances brought temporal to 100% (4/4) - target exceeded!

## References

- Design doc: `designs/2026-01-16-tlaps-benchmark-schema.md`
- Tactic implementations: `crates/clean-tla/src/tactic.rs`
- Obligation types: `crates/clean-tla/src/obligation.rs`
