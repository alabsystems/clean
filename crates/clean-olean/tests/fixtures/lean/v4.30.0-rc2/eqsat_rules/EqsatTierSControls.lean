/- EqsatTierSControls: what the saturation tier's rule set shares with the
   integer rule set (PKG-U4c).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   trust-cg `crates/trust-cg-eqsat/rules/tier_s_integer.rules` and
   `rules/integer_identities.rules` both have a rule `add_zero` and a rule
   `mul_one`, written with the same text. Each file's rule is quoted in its
   own generated module (`TierSDefs.add_zero`, `Defs.add_zero`). The
   statements here say the two literals of each pair are one term, so
   `Sound TierSDefs.add_zero T` and `Sound Defs.add_zero T` are one
   proposition and the one lemma `EqsatInt.add_zero` proves both (the gate
   asserts it on Clean's entry, at every integer type). That is why `LEMMAS`
   has one row for each of the two names.

   The gate requires each theorem of this module by name with its statement
   pinned (`STATEMENTS`). A rule file edited on one side only makes the
   regenerated literal another term: the theorem then does not compile, and
   `gen_rule_defs.py --lemmas` refuses the table until the later file's rule
   has a name, and a lemma, of its own.

   No other rule name is in both files; the gate compares the two generated
   modules' names.
-/
import EqsatIntRuleDefs
import EqsatTierSRuleDefs

namespace EqsatTierSControls
open EqsatRule

/-- The saturation tier's `add_zero` is the integer rule set's `add_zero`:
    one literal under two names. -/
theorem add_zero_is_the_integer_rule : TierSDefs.add_zero = Defs.add_zero := rfl

/-- The saturation tier's `mul_one` is the integer rule set's `mul_one`: one
    literal under two names. -/
theorem mul_one_is_the_integer_rule : TierSDefs.mul_one = Defs.mul_one := rfl

end EqsatTierSControls
