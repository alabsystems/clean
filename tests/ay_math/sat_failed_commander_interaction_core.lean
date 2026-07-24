-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for failed-literal probing interacting with
-- commander cardinality encodings. Failed probes derive unit facts that can
-- strengthen commander guard side conditions while preserving the AMO/equisat
-- skeleton around the commander split.

def AyFailedCommanderConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyFailedCommanderDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyFailedCommanderEquisat (before : Prop) (after : Prop) :=
  AyFailedCommanderConj (before -> after) (after -> before)

def AyFailedCommanderProbe (rest : Prop) (literal : Prop) :=
  rest -> literal -> False

def AyFailedCommanderGroup2
    (x : Prop) (y : Prop) (cmd : Prop) :=
  AyFailedCommanderConj
    (AyFailedCommanderDisj (Not x) (Not y))
    (AyFailedCommanderConj
      (AyFailedCommanderDisj (Not x) cmd)
      (AyFailedCommanderDisj (Not y) cmd))

def AyFailedCommanderSplit2x2
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyFailedCommanderConj
    (AyFailedCommanderGroup2 a b cmdAB)
    (AyFailedCommanderConj
      (AyFailedCommanderGroup2 c d cmdCD)
      (AyFailedCommanderDisj (Not cmdAB) (Not cmdCD)))

def AyFailedCommanderAtMostOne4
    (a : Prop) (b : Prop) (c : Prop) (d : Prop) :=
  AyFailedCommanderConj
    (a -> b -> False)
    (AyFailedCommanderConj
      (a -> c -> False)
      (AyFailedCommanderConj
        (a -> d -> False)
        (AyFailedCommanderConj
          (b -> c -> False)
          (AyFailedCommanderConj
            (b -> d -> False)
            (c -> d -> False)))))

def AyFailedCommanderContext
    (rest : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyFailedCommanderConj rest
    (AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD)

def AyFailedCommanderContextWithUnits
    (rest : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :=
  AyFailedCommanderConj rest
    (AyFailedCommanderConj
      (Not a)
      (AyFailedCommanderConj
        (Not c)
        (AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD)))

def AyFailedCommanderStrengthenedSide
    (a : Prop) (c : Prop) (cmdAB : Prop) (cmdCD : Prop) :=
  AyFailedCommanderConj
    (AyFailedCommanderDisj (Not a) cmdAB)
    (AyFailedCommanderDisj (Not c) cmdCD)

theorem ay_failed_commander_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyFailedCommanderConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_failed_commander_disj_left
    (left : Prop) (right : Prop) :
    left -> AyFailedCommanderDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_failed_commander_pair_forbids
    (left : Prop) (right : Prop) :
    AyFailedCommanderDisj (Not left) (Not right) ->
    left -> right -> False := by
  intro pairClause
  intro hleft
  intro hright
  exact pairClause False
    (fun notLeft => notLeft hleft)
    (fun notRight => notRight hright)

theorem ay_failed_commander_guard_implies_cmd
    (literal : Prop) (cmd : Prop) :
    AyFailedCommanderDisj (Not literal) cmd ->
    literal ->
    cmd := by
  intro guard
  intro hliteral
  exact guard cmd
    (fun notLiteral => False.elim (notLiteral hliteral))
    (fun hcmd => hcmd)

theorem ay_failed_commander_failed_unit
    (rest : Prop) (literal : Prop) :
    AyFailedCommanderProbe rest literal ->
    rest ->
    Not literal :=
  fun failed restH literalH =>
    failed restH literalH

theorem ay_failed_commander_unit_strengthens_guard
    (rest : Prop) (literal : Prop) (cmd : Prop) :
    AyFailedCommanderProbe rest literal ->
    rest ->
    AyFailedCommanderDisj (Not literal) cmd :=
  fun failed restH =>
    ay_failed_commander_disj_left (Not literal) cmd
      (ay_failed_commander_failed_unit rest literal failed restH)

theorem ay_failed_commander_units_strengthen_side
    (rest : Prop) (a : Prop) (c : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderProbe rest a ->
    AyFailedCommanderProbe rest c ->
    rest ->
    AyFailedCommanderStrengthenedSide a c cmdAB cmdCD := by
  intro failedA
  intro failedC
  intro restH
  exact ay_failed_commander_conj_intro
    (AyFailedCommanderDisj (Not a) cmdAB)
    (AyFailedCommanderDisj (Not c) cmdCD)
    (ay_failed_commander_unit_strengthens_guard
      rest a cmdAB failedA restH)
    (ay_failed_commander_unit_strengthens_guard
      rest c cmdCD failedC restH)

theorem ay_failed_commander_group_local_forbids
    (x : Prop) (y : Prop) (cmd : Prop) :
    AyFailedCommanderGroup2 x y cmd ->
    x -> y -> False :=
  fun groupH hx hy =>
    groupH False
    (fun pairClause _guards =>
      ay_failed_commander_pair_forbids x y pairClause hx hy)

theorem ay_failed_commander_cross_forbids
    (x : Prop) (y : Prop) (cmdX : Prop) (cmdY : Prop) :
    AyFailedCommanderGroup2 x y cmdX ->
    AyFailedCommanderGroup2 y x cmdY ->
    AyFailedCommanderDisj (Not cmdX) (Not cmdY) ->
    x -> y -> False := by
  intro groupX
  intro groupY
  intro commanderAmo
  intro hx
  intro hy
  exact commanderAmo False
    (fun notCmdX =>
      notCmdX
        (groupX cmdX
          (fun _pair guards =>
            guards cmdX
              (fun xGuard _yGuard =>
                ay_failed_commander_guard_implies_cmd
                  x cmdX xGuard hx))))
    (fun notCmdY =>
      notCmdY
        (groupY cmdY
          (fun _pair guards =>
            guards cmdY
              (fun yGuard _xGuard =>
                ay_failed_commander_guard_implies_cmd
                  y cmdY yGuard hy))))

theorem ay_failed_commander_split_ab_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD ->
    a -> b -> False :=
  fun splitH ha hb =>
    splitH False
    (fun groupAB _tail =>
      ay_failed_commander_group_local_forbids
        a b cmdAB groupAB ha hb)

theorem ay_failed_commander_split_cd_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD ->
    c -> d -> False :=
  fun splitH hc hd =>
    splitH False
    (fun _groupAB tail =>
      tail False
        (fun groupCD _commanderAmo =>
          ay_failed_commander_group_local_forbids
            c d cmdCD groupCD hc hd))

theorem ay_failed_commander_split_ac_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD ->
    a -> c -> False :=
  fun splitH ha hc =>
    splitH False
    (fun groupAB tail =>
      tail False
        (fun groupCD commanderAmo =>
          commanderAmo False
            (fun notCmdAB =>
              notCmdAB
                (groupAB cmdAB
                  (fun _pair guards =>
                    guards cmdAB
                      (fun aGuard _bGuard =>
                        ay_failed_commander_guard_implies_cmd
                          a cmdAB aGuard ha))))
            (fun notCmdCD =>
              notCmdCD
                (groupCD cmdCD
                  (fun _pair guards =>
                    guards cmdCD
                      (fun cGuard _dGuard =>
                        ay_failed_commander_guard_implies_cmd
                          c cmdCD cGuard hc))))))

theorem ay_failed_commander_split_ad_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD ->
    a -> d -> False :=
  fun splitH ha hd =>
    splitH False
    (fun groupAB tail =>
      tail False
        (fun groupCD commanderAmo =>
          commanderAmo False
            (fun notCmdAB =>
              notCmdAB
                (groupAB cmdAB
                  (fun _pair guards =>
                    guards cmdAB
                      (fun aGuard _bGuard =>
                        ay_failed_commander_guard_implies_cmd
                          a cmdAB aGuard ha))))
            (fun notCmdCD =>
              notCmdCD
                (groupCD cmdCD
                  (fun _pair guards =>
                    guards cmdCD
                      (fun _cGuard dGuard =>
                        ay_failed_commander_guard_implies_cmd
                          d cmdCD dGuard hd))))))

theorem ay_failed_commander_split_bc_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD ->
    b -> c -> False :=
  fun splitH hb hc =>
    splitH False
    (fun groupAB tail =>
      tail False
        (fun groupCD commanderAmo =>
          commanderAmo False
            (fun notCmdAB =>
              notCmdAB
                (groupAB cmdAB
                  (fun _pair guards =>
                    guards cmdAB
                      (fun _aGuard bGuard =>
                        ay_failed_commander_guard_implies_cmd
                          b cmdAB bGuard hb))))
            (fun notCmdCD =>
              notCmdCD
                (groupCD cmdCD
                  (fun _pair guards =>
                    guards cmdCD
                      (fun cGuard _dGuard =>
                        ay_failed_commander_guard_implies_cmd
                          c cmdCD cGuard hc))))))

theorem ay_failed_commander_split_bd_forbids
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD ->
    b -> d -> False :=
  fun splitH hb hd =>
    splitH False
    (fun groupAB tail =>
      tail False
        (fun groupCD commanderAmo =>
          commanderAmo False
            (fun notCmdAB =>
              notCmdAB
                (groupAB cmdAB
                  (fun _pair guards =>
                    guards cmdAB
                      (fun _aGuard bGuard =>
                        ay_failed_commander_guard_implies_cmd
                          b cmdAB bGuard hb))))
            (fun notCmdCD =>
              notCmdCD
                (groupCD cmdCD
                  (fun _pair guards =>
                    guards cmdCD
                      (fun _cGuard dGuard =>
                        ay_failed_commander_guard_implies_cmd
                          d cmdCD dGuard hd))))))

theorem ay_failed_commander_split_amo4_sound
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD ->
    AyFailedCommanderAtMostOne4 a b c d :=
  fun splitH =>
    ay_failed_commander_conj_intro
    (a -> b -> False)
    (AyFailedCommanderConj
      (a -> c -> False)
      (AyFailedCommanderConj
        (a -> d -> False)
        (AyFailedCommanderConj
          (b -> c -> False)
          (AyFailedCommanderConj
            (b -> d -> False)
            (c -> d -> False)))))
    (ay_failed_commander_split_ab_forbids
      a b c d cmdAB cmdCD splitH)
    (ay_failed_commander_conj_intro
      (a -> c -> False)
      (AyFailedCommanderConj
        (a -> d -> False)
        (AyFailedCommanderConj
          (b -> c -> False)
          (AyFailedCommanderConj
            (b -> d -> False)
            (c -> d -> False))))
      (ay_failed_commander_split_ac_forbids
        a b c d cmdAB cmdCD splitH)
      (ay_failed_commander_conj_intro
        (a -> d -> False)
        (AyFailedCommanderConj
          (b -> c -> False)
          (AyFailedCommanderConj
            (b -> d -> False)
            (c -> d -> False)))
        (ay_failed_commander_split_ad_forbids
          a b c d cmdAB cmdCD splitH)
        (ay_failed_commander_conj_intro
          (b -> c -> False)
          (AyFailedCommanderConj
            (b -> d -> False)
            (c -> d -> False))
          (ay_failed_commander_split_bc_forbids
            a b c d cmdAB cmdCD splitH)
          (ay_failed_commander_conj_intro
            (b -> d -> False)
            (c -> d -> False)
            (ay_failed_commander_split_bd_forbids
              a b c d cmdAB cmdCD splitH)
            (ay_failed_commander_split_cd_forbids
              a b c d cmdAB cmdCD splitH)))))

theorem ay_failed_commander_context_amo_sound
    (rest : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderContextWithUnits rest a b c d cmdAB cmdCD ->
    AyFailedCommanderAtMostOne4 a b c d := by
  intro strengthened
  exact strengthened (AyFailedCommanderAtMostOne4 a b c d)
    (fun _restH tail =>
      tail (AyFailedCommanderAtMostOne4 a b c d)
        (fun _notA tail2 =>
          tail2 (AyFailedCommanderAtMostOne4 a b c d)
            (fun _notC splitH =>
              ay_failed_commander_split_amo4_sound
                a b c d cmdAB cmdCD splitH)))

theorem ay_failed_commander_add_units_forward
    (rest : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderProbe rest a ->
    AyFailedCommanderProbe rest c ->
    AyFailedCommanderContext rest a b c d cmdAB cmdCD ->
    AyFailedCommanderContextWithUnits rest a b c d cmdAB cmdCD := by
  intro failedA
  intro failedC
  intro context
  exact context
    (AyFailedCommanderContextWithUnits rest a b c d cmdAB cmdCD)
    (fun restH splitH =>
      ay_failed_commander_conj_intro rest
        (AyFailedCommanderConj
          (Not a)
          (AyFailedCommanderConj
            (Not c)
            (AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD)))
        restH
        (ay_failed_commander_conj_intro
          (Not a)
          (AyFailedCommanderConj
            (Not c)
            (AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD))
          (ay_failed_commander_failed_unit rest a failedA restH)
          (ay_failed_commander_conj_intro
            (Not c)
            (AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD)
            (ay_failed_commander_failed_unit rest c failedC restH)
            splitH)))

theorem ay_failed_commander_add_units_backward
    (rest : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderContextWithUnits rest a b c d cmdAB cmdCD ->
    AyFailedCommanderContext rest a b c d cmdAB cmdCD := by
  intro strengthened
  exact strengthened
    (AyFailedCommanderContext rest a b c d cmdAB cmdCD)
    (fun restH tail =>
      tail (AyFailedCommanderContext rest a b c d cmdAB cmdCD)
        (fun _notA tail2 =>
          tail2 (AyFailedCommanderContext rest a b c d cmdAB cmdCD)
            (fun _notC splitH =>
              ay_failed_commander_conj_intro rest
                (AyFailedCommanderSplit2x2 a b c d cmdAB cmdCD)
                restH
                splitH)))

theorem ay_failed_commander_add_units_equisat
    (rest : Prop)
    (a : Prop) (b : Prop) (c : Prop) (d : Prop)
    (cmdAB : Prop) (cmdCD : Prop) :
    AyFailedCommanderProbe rest a ->
    AyFailedCommanderProbe rest c ->
    AyFailedCommanderEquisat
      (AyFailedCommanderContext rest a b c d cmdAB cmdCD)
      (AyFailedCommanderContextWithUnits rest a b c d cmdAB cmdCD) :=
  fun failedA failedC result keep =>
    keep
      (ay_failed_commander_add_units_forward
        rest a b c d cmdAB cmdCD failedA failedC)
      (ay_failed_commander_add_units_backward
        rest a b c d cmdAB cmdCD)
