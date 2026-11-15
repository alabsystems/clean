//! Added in Clean (not part of upstream Carcara): the resource budget of a step that expands a
//! bit-vector or a polynomial.
//!
//! A bit-vector width is a `usize`, and the parser accepts any positive one, so a step over
//! `((_ zero_extend 4294967295) #b0)` is well formed. The bit-blasting rules build one term per bit
//! of such a term (the multiplier and the divider one per pair of bits), and `poly_simp` and
//! `aci_simp` compute `2^w`. Unbounded, a step whose text is a few dozen bytes ran the checker out
//! of memory, or, for a `2^w` past GMP's integer type, into GMP's abort. A shared (`:named`)
//! subterm does the same at any width: an n-ary step reads one `@bbterm` n times, `poly_simp`
//! multiplies out a product of sums, and `aci_simp` flattens a sum of two copies of a sum of two
//! copies, each to sizes exponential in the step's text. The cost of a step is therefore counted
//! in *expanded bits* before anything is built, and a step that would expand more than
//! [`MAX_EXPANDED_BITS`] is refused with [`CheckerError::ResourceBudgetExceeded`]. A step within
//! the budget is checked exactly as before: the budget only decides whether the check runs.
//!
//! What a step is charged, in expanded bits (`w` is the width; each charge is made before the
//! terms it counts are built):
//!
//! - `w` for each bit-vector term whose bits it reads, split into `@bit_of`/`@int_of` terms or
//!   spelled out by the proof as a `@bbterm`/`@pbbterm` (a rule builds terms over every bit it
//!   reads, and an n-ary step can read one shared `@bbterm` n times);
//! - `i` for the bits `((_ sign_extend i) x)` adds;
//! - `w` for each stage of the barrel shifter (`ceil(log2 w)` stages and the final selection);
//! - `w * w` for each product of the shift-and-add multiplier;
//! - [`DIVIDER_BITS_PER_STEP_BIT`]` * w` for each of the divider's steps (at most `w`);
//! - `w` for each `2^w` constant;
//! - in words (below), for `poly_simp`: one for each term it visits (it walks shared subterms once
//!   per path to them) plus the 64-bit words of the coefficient it carries and of the numeral it
//!   reads; [`MONOMIAL_WORDS`] for each monomial entry it builds (an atom's, each pair's of a
//!   product, a constant counting as a monomial of degree 0 unless it is zero, and each moved out
//!   of a product), plus its factors and coefficient words; and, reducing a bit-vector polynomial
//!   modulo `2^w`, `w / 64` for each negative coefficient, which becomes a `w`-bit number
//!   (`checker/rules/polynomial.rs`);
//! - in words, for `aci_simp`, one for each argument a flattening builds
//!   (`checker/rules/simplification.rs`);
//! - in words, for `qnt_cnf`, before it prenexes and converts to conjunctive normal form, for each
//!   conjunction, disjunction and literal, once per path to it, the clauses of the normal form it
//!   builds times their most literals plus one, and for each universal quantifier, once per path
//!   to it, eight for each variable it binds (the prenexing walks copy them)
//!   (`checker/rules/quantifier.rs`);
//! - for `bfun_elim`, for a quantifier over `k > 0` Boolean variables, in words, a bit for each of
//!   its `2^k` instances' places in the conjunction, and for each pair of a subterm of the body
//!   and its mask (the variables it mentions that its context has not rebound, when there is one),
//!   `2^|mask|` times a bit plus the words the rebuilt term copies, its argument list and the names
//!   it binds (the terms its instances build, each once per assignment of its mask); and `2^m`
//!   times the arguments plus one for an application to `m > 0` Boolean arguments that are not
//!   constants (its `ite` tree over `2^m` copies) (`checker/rules/clausification.rs`);
//! - in words, for the string rules, for each flattening of a `str.++` application or a string
//!   constant, one for each term the walk visits, once per path to it, and one for each character
//!   past the first a split constant becomes (`checker/rules/strings.rs`);
//! - in words, for `evaluate`, each value it reads and computes (one word, and one for each 64
//!   bits of its numbers), and before a sum, difference, product or quotient is computed, twice
//!   the words its arguments' bits together can reach (the result, and GMP's work space)
//!   (`ast/evaluate.rs`);
//! - in words, for the linear combinations `la_generic`, `bounded_farkas` and `la_tautology` read,
//!   as for `poly_simp`'s walk: one for each term visited (once per path to it) plus the words of
//!   the coefficient it carries and of each numeral it reads
//!   (`checker/rules/linear_arithmetic.rs`).
//!
//! A step's cost is the sum of its charges. Bit-blasting a `w`-bit comparison, a bitwise operation
//! or an addition of two operands costs `2w`, so those rules check widths up to
//! `MAX_EXPANDED_BITS / 2`; the multiplier and the divider are quadratic, and check widths up to
//! about `sqrt(MAX_EXPANDED_BITS)` and half that. The linear work done per charged bit (carry
//! chains, comparison chains, selections) is a small constant, so the charge bounds the terms a
//! step builds.
//!
//! `poly_simp`, `aci_simp`, `qnt_cnf`, the string rules and `bfun_elim`'s argument lists build
//! words and pointers, not terms per bit, so they are charged in words, [`WORDS_PER_EXPANDED_BIT`] (64) to an expanded bit: such a step may use `2^24`
//! of them. So are `evaluate`'s numbers and the linear arithmetic rules' walks. The rate is measured, not assumed: a bit-blasted bit costs about 2.3 KB at the budget
//! (`bitblast_neg` peaks at 601 MB at `2^18` bits), and a word charged to one of these rules at
//! most about 12 bytes at theirs (their costliest admitted steps peak at 197 MB), so none of them
//! peaks above what bit-blasting does. Charged a bit a unit, they refused steps of a few kilobytes
//! that check in a few megabytes (DOWNSTREAM.md, "Words").
//!
//! What the budget bounds is one step. Across steps: the checker stops at the first step it
//! refuses, for any reason, and the terms an accepted bit-blasting step builds are those of its
//! conclusion, which the proof spells out, up to a constant factor (the divider's discarded sums,
//! an n-ary step's intermediate `@bbterm`s), as are `bfun_elim`'s instances; `poly_simp` keeps
//! nothing past its step, nor do `aci_simp` and the string rules, whose flattenings (not part of
//! their conclusions) are built in a `StepTerms` the step owns, not added to the pool, where they stayed for the rest of
//! the proof (a 1.2 MB proof of 2,000 accepted steps over distinct shared sums kept 2 GB), nor
//! `qnt_cnf`, which compares its clauses with the conclusion's without adding them to it, nor
//! `evaluate`, whose values are built in a `StepTerms` too. The
//! budget does not bound time across steps: a proof can repeat a step within the budget, each time
//! naming its (already parsed) conclusion. That is what the check's deadline is for
//! (`checker/deadline.rs`). The checker's other rules are not charged.
//!
//! The bound, the measurements behind it, and what it refuses are in
//! third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a resource budget". Beside its
//! charges, `evaluate` keeps its width bound, `MAX_EVALUATED_BV_WIDTH` in `ast/evaluate.rs` (fix
//! 35), which makes its casts of widths and bit indices exact; that bound covers bit-vectors and
//! `int.pow2`, not the integers and rationals arithmetic computes, which only the charges bound.

use super::error::CheckerError;

/// The most bits one step may expand bit-vector terms into (see the module documentation). The
/// costliest step of trust-cg's 5,441 proof-gate certificates costs 16,640 (a 128-bit
/// multiplication of spelled-out operands), almost sixteen times less; a step at this budget
/// peaks at about 600 MB and checks in under a second (DOWNSTREAM.md has the measurements).
pub const MAX_EXPANDED_BITS: u128 = 1 << 18;

/// What an expanded bit is worth in the words and pointers `poly_simp`, `aci_simp` and `qnt_cnf`
/// are charged (see the module documentation): a bit-blasted bit costs about 2.3 KB at the budget,
/// a word charged to those rules at most about 12 bytes, so they may use `2^24` words a step.
pub const WORDS_PER_EXPANDED_BIT: u128 = 64;

/// The words `poly_simp` is charged for each monomial entry it builds, beside the monomial's
/// factors and its coefficient's words: the map's bucket (its hash, the factor list and the
/// coefficient, eight words), its index slot, and the heap blocks of the factor list and of the
/// coefficient's numerator and denominator. Measured, a polynomial of monomials of two factors
/// takes about 240 bytes a monomial at its peak, with the map's growth.
pub const MONOMIAL_WORDS: u128 = 16;

/// What one step of the divider costs per bit of the width, relative to a bit of an operand. A step
/// builds three ripple-carry adders and two selections over every bit, about four times the memory
/// a bit of a bit-blasted comparison takes.
pub const DIVIDER_BITS_PER_STEP_BIT: u128 = 4;

/// What a step refused by the budget would have expanded: carried by
/// [`CheckerError::ResourceBudgetExceeded`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BudgetExceeded {
    /// What the refused charge was for.
    pub what: &'static str,
    /// The expanded bits the step would have reached with it.
    pub needed: u128,
    /// The budget, [`MAX_EXPANDED_BITS`].
    pub budget: u128,
}

impl std::fmt::Display for BudgetExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{} would bring the step to {} expanded bits, more than the {} one step may use",
            self.what, self.needed, self.budget
        )
    }
}

/// The expanded bits charged to one step so far, kept in words: an expanded bit is
/// [`WORDS_PER_EXPANDED_BIT`] of them.
#[derive(Debug, Default)]
pub(crate) struct ExpansionBudget {
    spent_words: u128,
}

impl ExpansionBudget {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Charges `bits` expanded bits for `what`, or refuses the step if its total would exceed
    /// [`MAX_EXPANDED_BITS`].
    pub(crate) fn spend(&mut self, what: &'static str, bits: u128) -> Result<(), CheckerError> {
        self.spend_words(what, bits.saturating_mul(WORDS_PER_EXPANDED_BIT))
    }

    /// Charges `words` words for `what` ([`WORDS_PER_EXPANDED_BIT`] of them to an expanded bit),
    /// or refuses the step if its total would exceed [`MAX_EXPANDED_BITS`]. A refusal names the
    /// expanded bits the step would have reached, rounded up.
    pub(crate) fn spend_words(
        &mut self,
        what: &'static str,
        words: u128,
    ) -> Result<(), CheckerError> {
        let needed = self.spent_words.saturating_add(words);
        if needed > MAX_EXPANDED_BITS * WORDS_PER_EXPANDED_BIT {
            return Err(CheckerError::ResourceBudgetExceeded(Box::new(
                BudgetExceeded {
                    what,
                    needed: needed.div_ceil(WORDS_PER_EXPANDED_BIT),
                    budget: MAX_EXPANDED_BITS,
                },
            )));
        }
        self.spent_words = needed;
        Ok(())
    }

    /// Charges one bit per bit of a `width`-bit term.
    pub(crate) fn spend_width(
        &mut self,
        what: &'static str,
        width: usize,
    ) -> Result<(), CheckerError> {
        self.spend(what, width as u128)
    }
}

/// The 64-bit words a rational's numerator and denominator take, rounded down (`0` and `1` cost
/// nothing).
pub(crate) fn rational_words(r: &rug::Rational) -> u128 {
    (u128::from(r.numer().significant_bits()) + u128::from(r.denom().significant_bits())) / 64
}

/// The 64-bit words an integer takes, rounded down.
pub(crate) fn integer_words(i: &rug::Integer) -> u128 {
    u128::from(i.significant_bits()) / 64
}

/// Whether `c` is `2^i`, without computing `2^i`: a step reading a coefficient against a bit
/// position taken from a sort of width `2^40` would otherwise build a 128 GiB integer to compare
/// with.
pub(crate) fn is_two_to_the(c: &rug::Integer, i: usize) -> bool {
    // `2^i` is positive, has a single one bit, and needs `i + 1` bits. A position whose `i + 1` is
    // past `u32` is answered `false`, the closed side: `2^i` would be a numeral of more than
    // 512 MiB, which `significant_bits` cannot count.
    i.checked_add(1)
        .and_then(|bits| u32::try_from(bits).ok())
        .is_some_and(|bits| c.is_power_of_two() && c.significant_bits() == bits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::Integer;

    #[test]
    fn spending_past_the_budget_is_refused_and_the_edge_is_not() {
        let mut budget = ExpansionBudget::new();
        budget.spend("half", MAX_EXPANDED_BITS / 2).unwrap();
        budget.spend("the rest", MAX_EXPANDED_BITS / 2).unwrap();
        let error = budget.spend("one more", 1).unwrap_err();
        assert!(matches!(
            error,
            CheckerError::ResourceBudgetExceeded(b) if b.needed == MAX_EXPANDED_BITS + 1
        ));
        assert!(ExpansionBudget::new().spend("all", u128::MAX).is_err());
    }

    #[test]
    fn words_are_charged_at_their_rate_and_a_refusal_rounds_up() {
        let mut budget = ExpansionBudget::new();
        budget.spend("one bit", 1).unwrap();
        let rest = (MAX_EXPANDED_BITS - 1) * WORDS_PER_EXPANDED_BIT;
        budget.spend_words("the rest in words", rest).unwrap();
        let error = budget.spend_words("one word more", 1).unwrap_err();
        assert!(matches!(
            error,
            CheckerError::ResourceBudgetExceeded(b) if b.needed == MAX_EXPANDED_BITS + 1
        ));
        assert!(ExpansionBudget::new()
            .spend_words("all", u128::MAX)
            .is_err());
    }

    #[test]
    fn is_two_to_the_agrees_with_shifting() {
        let mut values: Vec<Integer> = (-70..=70).map(Integer::from).collect();
        for e in 0..=200u32 {
            let p = Integer::from(1) << e;
            values.extend([p.clone() - 1, p.clone(), p.clone() + 1, -p.clone(), p * 3]);
        }
        for c in &values {
            for i in 0..=210usize {
                assert_eq!(
                    is_two_to_the(c, i),
                    *c == (Integer::from(1) << i),
                    "c = {c}, i = {i}"
                );
            }
        }
        assert!(!is_two_to_the(&Integer::from(1), usize::MAX));
    }
}
