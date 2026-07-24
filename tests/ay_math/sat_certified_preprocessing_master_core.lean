-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Master preprocessing-certificate composition skeleton for SAT-COMP math.
-- Each concrete transformation contributes an abstract equisat certificate;
-- this file proves that the certificates compose through visible reconstruction.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyForwardMap (before : Prop) (after : Prop) :=
  before -> after

def AyBackwardMap (before : Prop) (after : Prop) :=
  after -> before

def AyBveCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyBceCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyVivificationCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyHbrCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyBackboneUnitCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyCommanderCardinalityCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyTseitinCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyXorReasoningCertificate (before : Prop) (after : Prop) :=
  AyEquisat before after

def AyVisibleModelReconstruction (internalFinal : Prop) (visibleFinal : Prop) :=
  AyEquisat internalFinal visibleFinal

def AyMasterPreprocessingCertificate
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :=
  AyConj
    (AyBveCertificate input bve)
    (AyConj
      (AyBceCertificate bve bce)
      (AyConj
        (AyVivificationCertificate bce viv)
        (AyConj
          (AyHbrCertificate viv hbr)
          (AyConj
            (AyBackboneUnitCertificate hbr backbone)
            (AyConj
              (AyCommanderCardinalityCertificate backbone commander)
              (AyConj
                (AyTseitinCertificate commander tseitin)
                (AyConj
                  (AyXorReasoningCertificate tseitin xor)
                  (AyVisibleModelReconstruction xor visible))))))))

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun hp _hq => hp)

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    AyForwardMap before after ->
    AyBackwardMap before after ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    AyForwardMap before after := by
  intro equisat
  exact equisat (before -> after)
    (fun forward _backward => forward)

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    AyBackwardMap before after := by
  intro equisat
  exact equisat (after -> before)
    (fun _forward backward => backward)

theorem ay_forward_compose
    (first : Prop) (middle : Prop) (last : Prop) :
    AyForwardMap first middle ->
    AyForwardMap middle last ->
    AyForwardMap first last := by
  intro first_middle
  intro middle_last
  intro hfirst
  exact middle_last (first_middle hfirst)

theorem ay_backward_compose
    (first : Prop) (middle : Prop) (last : Prop) :
    AyBackwardMap first middle ->
    AyBackwardMap middle last ->
    AyBackwardMap first last := by
  intro middle_first
  intro last_middle
  intro hlast
  exact middle_first (last_middle hlast)

theorem ay_equisat_trans
    (first : Prop) (middle : Prop) (last : Prop) :
    AyEquisat first middle ->
    AyEquisat middle last ->
    AyEquisat first last := by
  intro first_middle
  intro middle_last
  exact ay_equisat_intro first last
    (ay_forward_compose first middle last
      (ay_equisat_forward first middle first_middle)
      (ay_equisat_forward middle last middle_last))
    (ay_backward_compose first middle last
      (ay_equisat_backward first middle first_middle)
      (ay_equisat_backward middle last middle_last))

theorem ay_stage_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before -> after := by
  intro stage
  exact ay_equisat_forward before after stage

theorem ay_stage_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after -> before := by
  intro stage
  exact ay_equisat_backward before after stage

theorem ay_master_project_bve
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyBveCertificate input bve := by
  intro cert
  exact cert (AyBveCertificate input bve)
    (fun bve_stage _tail => bve_stage)

theorem ay_master_project_bce
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyBceCertificate bve bce := by
  intro cert
  exact cert (AyBceCertificate bve bce)
    (fun _bve_stage tail =>
      tail (AyBceCertificate bve bce)
        (fun bce_stage _tail2 => bce_stage))

theorem ay_master_project_vivification
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyVivificationCertificate bce viv := by
  intro cert
  exact cert (AyVivificationCertificate bce viv)
    (fun _bve_stage tail =>
      tail (AyVivificationCertificate bce viv)
        (fun _bce_stage tail2 =>
          tail2 (AyVivificationCertificate bce viv)
            (fun viv_stage _tail3 => viv_stage)))

theorem ay_master_project_hbr
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyHbrCertificate viv hbr := by
  intro cert
  exact cert (AyHbrCertificate viv hbr)
    (fun _bve_stage tail =>
      tail (AyHbrCertificate viv hbr)
        (fun _bce_stage tail2 =>
          tail2 (AyHbrCertificate viv hbr)
            (fun _viv_stage tail3 =>
              tail3 (AyHbrCertificate viv hbr)
                (fun hbr_stage _tail4 => hbr_stage))))

theorem ay_master_project_backbone
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyBackboneUnitCertificate hbr backbone := by
  intro cert
  exact cert (AyBackboneUnitCertificate hbr backbone)
    (fun _bve_stage tail =>
      tail (AyBackboneUnitCertificate hbr backbone)
        (fun _bce_stage tail2 =>
          tail2 (AyBackboneUnitCertificate hbr backbone)
            (fun _viv_stage tail3 =>
              tail3 (AyBackboneUnitCertificate hbr backbone)
                (fun _hbr_stage tail4 =>
                  tail4 (AyBackboneUnitCertificate hbr backbone)
                    (fun backbone_stage _tail5 => backbone_stage)))))

theorem ay_master_project_commander
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyCommanderCardinalityCertificate backbone commander := by
  intro cert
  exact cert (AyCommanderCardinalityCertificate backbone commander)
    (fun _bve_stage tail =>
      tail (AyCommanderCardinalityCertificate backbone commander)
        (fun _bce_stage tail2 =>
          tail2 (AyCommanderCardinalityCertificate backbone commander)
            (fun _viv_stage tail3 =>
              tail3 (AyCommanderCardinalityCertificate backbone commander)
                (fun _hbr_stage tail4 =>
                  tail4 (AyCommanderCardinalityCertificate backbone commander)
                    (fun _backbone_stage tail5 =>
                      tail5
                        (AyCommanderCardinalityCertificate backbone commander)
                        (fun commander_stage _tail6 =>
                          commander_stage)))))))

theorem ay_master_project_tseitin
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyTseitinCertificate commander tseitin := by
  intro cert
  exact cert (AyTseitinCertificate commander tseitin)
    (fun _bve_stage tail =>
      tail (AyTseitinCertificate commander tseitin)
        (fun _bce_stage tail2 =>
          tail2 (AyTseitinCertificate commander tseitin)
            (fun _viv_stage tail3 =>
              tail3 (AyTseitinCertificate commander tseitin)
                (fun _hbr_stage tail4 =>
                  tail4 (AyTseitinCertificate commander tseitin)
                    (fun _backbone_stage tail5 =>
                      tail5 (AyTseitinCertificate commander tseitin)
                        (fun _commander_stage tail6 =>
                          tail6 (AyTseitinCertificate commander tseitin)
                            (fun tseitin_stage _tail7 =>
                              tseitin_stage))))))))

theorem ay_master_project_xor
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyXorReasoningCertificate tseitin xor := by
  intro cert
  exact cert (AyXorReasoningCertificate tseitin xor)
    (fun _bve_stage tail =>
      tail (AyXorReasoningCertificate tseitin xor)
        (fun _bce_stage tail2 =>
          tail2 (AyXorReasoningCertificate tseitin xor)
            (fun _viv_stage tail3 =>
              tail3 (AyXorReasoningCertificate tseitin xor)
                (fun _hbr_stage tail4 =>
                  tail4 (AyXorReasoningCertificate tseitin xor)
                    (fun _backbone_stage tail5 =>
                      tail5 (AyXorReasoningCertificate tseitin xor)
                        (fun _commander_stage tail6 =>
                          tail6 (AyXorReasoningCertificate tseitin xor)
                            (fun _tseitin_stage tail7 =>
                              tail7 (AyXorReasoningCertificate tseitin xor)
                                (fun xor_stage _visible_stage =>
                                  xor_stage)))))))))

theorem ay_master_project_visible
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyVisibleModelReconstruction xor visible := by
  intro cert
  exact cert (AyVisibleModelReconstruction xor visible)
    (fun _bve_stage tail =>
      tail (AyVisibleModelReconstruction xor visible)
        (fun _bce_stage tail2 =>
          tail2 (AyVisibleModelReconstruction xor visible)
            (fun _viv_stage tail3 =>
              tail3 (AyVisibleModelReconstruction xor visible)
                (fun _hbr_stage tail4 =>
                  tail4 (AyVisibleModelReconstruction xor visible)
                    (fun _backbone_stage tail5 =>
                      tail5 (AyVisibleModelReconstruction xor visible)
                        (fun _commander_stage tail6 =>
                          tail6 (AyVisibleModelReconstruction xor visible)
                            (fun _tseitin_stage tail7 =>
                              tail7 (AyVisibleModelReconstruction xor visible)
                                (fun _xor_stage visible_stage =>
                                  visible_stage)))))))))

theorem ay_master_pipeline_forward_map
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyBveCertificate input bve ->
    AyBceCertificate bve bce ->
    AyVivificationCertificate bce viv ->
    AyHbrCertificate viv hbr ->
    AyBackboneUnitCertificate hbr backbone ->
    AyCommanderCardinalityCertificate backbone commander ->
    AyTseitinCertificate commander tseitin ->
    AyXorReasoningCertificate tseitin xor ->
    AyVisibleModelReconstruction xor visible ->
    input -> visible := by
  intro bve_stage
  intro bce_stage
  intro viv_stage
  intro hbr_stage
  intro backbone_stage
  intro commander_stage
  intro tseitin_stage
  intro xor_stage
  intro visible_stage
  intro hinput
  exact ay_equisat_forward xor visible visible_stage
    (ay_equisat_forward tseitin xor xor_stage
      (ay_equisat_forward commander tseitin tseitin_stage
        (ay_equisat_forward backbone commander commander_stage
          (ay_equisat_forward hbr backbone backbone_stage
            (ay_equisat_forward viv hbr hbr_stage
              (ay_equisat_forward bce viv viv_stage
                (ay_equisat_forward bve bce bce_stage
                  (ay_equisat_forward input bve bve_stage hinput))))))))

theorem ay_master_pipeline_backward_map
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyBveCertificate input bve ->
    AyBceCertificate bve bce ->
    AyVivificationCertificate bce viv ->
    AyHbrCertificate viv hbr ->
    AyBackboneUnitCertificate hbr backbone ->
    AyCommanderCardinalityCertificate backbone commander ->
    AyTseitinCertificate commander tseitin ->
    AyXorReasoningCertificate tseitin xor ->
    AyVisibleModelReconstruction xor visible ->
    visible -> input := by
  intro bve_stage
  intro bce_stage
  intro viv_stage
  intro hbr_stage
  intro backbone_stage
  intro commander_stage
  intro tseitin_stage
  intro xor_stage
  intro visible_stage
  intro hvisible
  exact ay_equisat_backward input bve bve_stage
    (ay_equisat_backward bve bce bce_stage
      (ay_equisat_backward bce viv viv_stage
        (ay_equisat_backward viv hbr hbr_stage
          (ay_equisat_backward hbr backbone backbone_stage
            (ay_equisat_backward backbone commander commander_stage
              (ay_equisat_backward commander tseitin tseitin_stage
                (ay_equisat_backward tseitin xor xor_stage
                  (ay_equisat_backward xor visible visible_stage
                    hvisible))))))))

theorem ay_master_pipeline_equisat
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyBveCertificate input bve ->
    AyBceCertificate bve bce ->
    AyVivificationCertificate bce viv ->
    AyHbrCertificate viv hbr ->
    AyBackboneUnitCertificate hbr backbone ->
    AyCommanderCardinalityCertificate backbone commander ->
    AyTseitinCertificate commander tseitin ->
    AyXorReasoningCertificate tseitin xor ->
    AyVisibleModelReconstruction xor visible ->
    AyEquisat input visible := by
  intro bve_stage
  intro bce_stage
  intro viv_stage
  intro hbr_stage
  intro backbone_stage
  intro commander_stage
  intro tseitin_stage
  intro xor_stage
  intro visible_stage
  exact ay_equisat_intro input visible
    (ay_master_pipeline_forward_map
      input bve bce viv hbr backbone commander tseitin xor visible
      bve_stage bce_stage viv_stage hbr_stage backbone_stage
      commander_stage tseitin_stage xor_stage visible_stage)
    (ay_master_pipeline_backward_map
      input bve bce viv hbr backbone commander tseitin xor visible
      bve_stage bce_stage viv_stage hbr_stage backbone_stage
      commander_stage tseitin_stage xor_stage visible_stage)

theorem ay_master_certificate_equisat
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    AyEquisat input visible := by
  intro cert
  exact ay_master_pipeline_equisat
    input bve bce viv hbr backbone commander tseitin xor visible
    (ay_master_project_bve
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_bce
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_vivification
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_hbr
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_backbone
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_commander
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_tseitin
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_xor
      input bve bce viv hbr backbone commander tseitin xor visible cert)
    (ay_master_project_visible
      input bve bce viv hbr backbone commander tseitin xor visible cert)

theorem ay_master_visible_model_reconstructs_input
    (input bve bce viv hbr backbone commander tseitin xor visible : Prop) :
    AyMasterPreprocessingCertificate
      input bve bce viv hbr backbone commander tseitin xor visible ->
    visible -> input := by
  intro cert
  exact ay_equisat_backward input visible
    (ay_master_certificate_equisat
      input bve bce viv hbr backbone commander tseitin xor visible cert)
