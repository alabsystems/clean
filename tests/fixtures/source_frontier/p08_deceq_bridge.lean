-- p08 — CLASS I, the `decEq` bridge.
--
-- RE-PINNED 2026-08-26 (FRONTIER STAGE I-1): FAIL -> PASS, 0/2 -> 2/0.
-- Renamed from `p08_deceq_bridge_MUST_FAIL.lean`. The flip is this stage's
-- exit criterion; the file is unchanged, only its pinned verdict moved.
--
-- WHAT IT PINNED BEFORE: `infer/instance.rs` already carried a bridge for
-- `Decidable (@Eq α a b)` — it recognised the shape and delegated to
-- `DecidableEq α`. The bridge FIRED and then died at the delegation, because
-- `DecidableEq α` was itself unresolvable (p11): the local-instance loop
-- whnf'd the `[DecidableEq α]` binder into a Pi, `extract_class_app` returned
-- `None`, and the binder was passed over in silence.
--
-- WHAT IT PINS NOW: the bridge reaches its dictionary. Match (A) of
-- `resolve_local_instance_telescoped` answers `DecidableEq α` from the local
-- whose declared type IS `DecidableEq α`, and the bridge applies it to `a b`.
-- `probe_local_inst` then goes through match (C), which is what p09 isolates.
--
-- WHAT IT DOES NOT ESTABLISH: that telescoped locals work in general — both
-- declarations here run through the hand-written `Decidable`/`Eq` bridge.
-- p23 is the probe that removes the bridge from the picture.
--
-- CONTROL: p12 — the same `[DecidableEq α]` local used as an explicit
-- argument worked before the repair and works after, so the local itself was
-- never the problem. p20 — the refusal half: a local at the WRONG carrier is
-- still not grabbed.
def usesDecEq {α : Type} [DecidableEq α] (a b : α) : Bool :=
  if a = b then true else false

theorem probe_local_inst {α : Type} [DecidableEq α] (a : α) : usesDecEq a a = usesDecEq a a := rfl
