-- p17 — CLASS II, the ARTIFACT FORM. p03's body inside a namespace.
--
-- PROVES: the message the CORPUS REPORT carries. Until 2026-08-27 that was not
-- the message the terminal printed: `clean check` rendered a top-level
-- declaration's failure with `{e:?}` (`crates/clean-cli/src/cmd_core.rs`, the
-- entry-file arm) but a declaration nested in a namespace or section — i.e.
-- every declaration in every Mathlib file — through the leaf arm's `{e}`, the
-- Display impl. So this probe, and only this probe, pinned what
-- `per_error_class` would actually hold:
--
--   Unknown identifier: Fr.MyInj.nosuchfield; dot notation `.nosuchfield` on a
--   receiver of type `Fr.MyInj …`, whose head does not name a type after
--   reduction (Pi)
--
-- WHY THAT STRING IS LOAD-BEARING: two of its properties decide the next corpus
-- reading.
--   1. `Unknown identifier:` LEADS, so `scripts/srcelab_classify.py`
--      (ordered, first-match-wins) files these under `unknown identifier`
--      instead of `not implemented (elaborator NYI)` — which is the whole
--      point of stage 0, and what recon §5.6 stage II-1 expects to read.
--   2. The name comes FIRST, so it survives `per_error_class`'s 400-char
--      truncation. The message it replaces put a raw `Expr` dump there, and
--      the truncation is why the class could not be triaged at all.
-- `dot notation` keeps them separable from the report's pre-existing
-- unknown-identifier population.
--
-- Reword this message and the next corpus run silently reclassifies 44 entries.
--
-- 2026-08-27, THE DIVERGENCE IS CLOSED. `cmd_core.rs` now renders BOTH paths
-- through one function (`elaboration_error_diagnostic`), Display in both, with
-- the line number in both. So this fixture no longer measures a form the
-- terminal cannot show — it measures that the two AGREE, and the battery pins
-- it twice on purpose: once from `clean check` (terminal) and once from
-- `clean check --json` (the report). If those two lines ever need different
-- fragments again, a second rendering path has grown back.
--
-- CONTROL: p03 is the same declaration at top level. Before the unification it
-- ruled out "the identifier is named only in one rendering"; it now also pins
-- that the top-level path prints the SAME form this one does.
namespace Fr

def MyInj (f : Nat → Nat) : Prop := ∀ a b : Nat, f a = f b → a = b

theorem probe_missing_field {f : Nat → Nat} (h : MyInj f) : True :=
  h.nosuchfield

end Fr
