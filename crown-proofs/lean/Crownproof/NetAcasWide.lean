/-
  ============================================================================
  WAVE-7 PROGRAM 1 — FULL WIDTH: the real ACAS-Xu first layer at FULL 50-NEURON
  WIDTH, with the real layer-1 readout summing over all 50 wide-layer neurons.
  ============================================================================

  Wave-6 (`NetAcas7Layer.lean`) reached all 7 real ACAS layers to the real Y_0
  but on a NARROW slice (widths {3,3,3,3,2,1}); its readout summed over ONE neuron.
  THIS file pushes WIDTH to the FULL 50:

    * L0 : the real first hidden affine+ReLU layer at the FULL 50-neuron width
           (real f32 weights, parsed losslessly from the ONNX), IBP-threaded from
           the input box — all 50 pre-activations and all 50 post-ReLU activations
           bounded exactly over ℚ.
    * Readout: `netEvalWide x = Σ_{j<50} Wr j · relu(z0_j) + br`, the REAL layer-1
           affine readout direction (row 0 of the real `Operation_2` layer) summing
           over ALL 50 layer-0 activations — a real WIDE readout (50→1), NOT one
           neuron.  This is the genuine real next-layer output direction at full
           width 50.

  DECISION (this one IS decided).  Over the dyadic prop_1 input box, the exact
  CROWN/IBP upper bound on this real full-width readout is
    cBound = 553630694887348241/288230376151711744 ≈ +1.9207923  <  3.991125645861615.
  So `netEvalWide_below_thr` proves the real layer-1 readout stays strictly below
  the prop_1 threshold everywhere on the box — a genuine full-width verdict on a
  real readout direction.  (Honesty: this is the real LAYER-1 direction, not the
  depth-7 Y_0 itself; see the wall note.)

  THE WALL toward the real depth-7 Y_0 (ruthlessly honest, all MEASURED):
    1. exact-CROWN backsubstitution coefficients EXPLODE with depth: ~2416 digits
       after one backsub (L5), ~5002 digits after all six layers — intractable in
       Lean.  One must use the looser IBP relaxation (bignums stay ~64 digits).
    2. Even with IBP, deeper full-width layers cost ~10 s/wide-neuron (≈ tens of
       minutes for the depth-6 chain), AND — the hard blocker — Lean's `simp`
       (`Matrix.cons_val` simproc) PANICs (`Lean.Expr.appArg!: application expected`)
       when a closed-form `simp` recurses into the deeply-nested real
       `relu(affine(relu(...)))` activation subterms.  The readout over the
       1-level-deep layer-0 activations below stays clear of that wall.
    3. The full-width real Y_0 itself does NOT decide prop_1 by any relaxation we
       computed: its full-width IBP upper bound ≈ +8029.42 (gap +8025.43 above the
       threshold), and even exact full CROWN ≈ +6389 (gap +6385).  prop_1 on this
       box is a hard property requiring branch-and-bound, not a single CROWN pass.

  WHAT THIS FILE PROVES (sorry-free; axioms = [propext, Classical.choice, Quot.sound]):
    * `netEvalWide` — the real full-width layer-1 readout (sum over all 50 L0 neurons).
    * `z0box_k` / `aBox0` — the full-width-50 IBP bounds (all 50 neurons).
    * `bridge_premises_sound` — every emitter box premise (a_j ≥ 0, a_j ≤ uz_j over
      all 50 layer-0 neurons) holds on every valid `netEvalWide` execution
      (Bridge.farkas_premise_combination form, 100 premises).
    * `netEvalWide_upper_bound` — netEvalWide x ≤ cBound on the whole box, via the
      Farkas combination of the 100 readout box premises (multipliers |Wr j|).
    * `netEvalWide_below_thr` — the DECISION: netEvalWide x < prop_1 threshold.

  Input box: the dyadic over-approximation of the VNN-COMP ACAS prop_1 box
  (contains the real decimal box), identical to wave-6.
-/
import Crownproof.Basic
import Crownproof.Bridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
namespace Crownproof
namespace NetAcasWide
open Crownproof Finset

def W0 : Fin 50 → Fin 5 → ℚ :=
  ![ ![ 14497179/268435456, -684437/262144, -12081407/67108864, 4063341/16777216, 9489663/67108864 ]
   , ![ -4713307/4194304, 14152937/536870912, -2464047/268435456, 14931185/268435456, -5496803/16777216 ]
   , ![ 3288653/16777216, 16251015/67108864, 10711447/16777216, -8023955/16777216, 9568181/67108864 ]
   , ![ -13674689/8388608, -9246179/268435456, -6501421/1073741824, 12034069/1073741824, -11273967/1073741824 ]
   , ![ -5958143/16777216, 1186923/2097152, 15318739/67108864, 2975305/16777216, -6981939/33554432 ]
   , ![ -9178291/268435456, 12546841/8388608, -3216423/2097152, 10873059/268435456, 5514671/33554432 ]
   , ![ 13488949/33554432, 7516931/33554432, -12540231/268435456, 1374809/8388608, -5396425/33554432 ]
   , ![ -2969043/2097152, -5015911/67108864, 16223863/268435456, 6478099/134217728, -15034963/268435456 ]
   , ![ -12121371/8388608, 6018363/134217728, 9544663/1073741824, -4198163/16777216, 8768605/134217728 ]
   , ![ -9457317/8388608, 6439525/268435456, -5136303/536870912, 2396581/268435456, -9835625/2147483648 ]
   , ![ 10296463/16777216, -9358667/16777216, -6972705/134217728, 10794595/67108864, -13042943/134217728 ]
   , ![ 7832435/8388608, 13666519/67108864, 11152017/67108864, -6535351/4294967296, -14055817/67108864 ]
   , ![ -10952865/268435456, 287659/524288, 15431495/268435456, 9595561/67108864, 12732981/134217728 ]
   , ![ -14244863/67108864, -5502977/16777216, 11996917/33554432, -13076665/33554432, -1926599/4194304 ]
   , ![ 4297383/134217728, 7087619/16777216, -4771717/8388608, -14145341/67108864, 10167073/134217728 ]
   , ![ -832519/67108864, 9582013/4194304, 1793877/33554432, 3896079/67108864, 7962601/67108864 ]
   , ![ -4108069/33554432, -5973041/8388608, 2458611/268435456, -6561955/16777216, 142543/4194304 ]
   , ![ 16152889/268435456, -8577479/134217728, -5248773/2097152, 13413773/268435456, -5072061/134217728 ]
   , ![ 11180793/134217728, -10938369/268435456, -12618161/16777216, -7972399/67108864, -14632685/67108864 ]
   , ![ -4983001/4194304, 9705955/67108864, -10018011/67108864, -9684239/268435456, -15962917/134217728 ]
   , ![ -13896501/134217728, 2348525/33554432, 2541465/1048576, 1520009/67108864, 8579331/268435456 ]
   , ![ -2865223/33554432, 734905/4194304, -5865375/67108864, -12278171/16777216, -14820993/67108864 ]
   , ![ -5203299/268435456, 16751631/4194304, 3952947/33554432, 10524629/134217728, -7794453/536870912 ]
   , ![ 4479275/268435456, -5489547/8388608, 2349213/4194304, 13192193/67108864, -15092951/33554432 ]
   , ![ 900005/536870912, 5781391/1073741824, -7802227/1073741824, 4489143/1073741824, 15299103/8589934592 ]
   , ![ -15057971/16777216, -4281747/33554432, 2731381/16777216, -12916685/268435456, 10542279/134217728 ]
   , ![ -7828417/8388608, -6530417/268435456, 15453359/67108864, -14027967/67108864, -12665617/134217728 ]
   , ![ 10759765/67108864, 247827/67108864, 8796261/33554432, 9460437/33554432, -1156529/2097152 ]
   , ![ 1399255/16777216, 8442337/4194304, 11922225/33554432, 9665421/268435456, -13374555/134217728 ]
   , ![ 595631/2097152, -3125535/67108864, 8030837/1073741824, -3525367/4194304, -4041539/8388608 ]
   , ![ 11517139/8388608, 12630425/2147483648, 14056139/1073741824, -9945601/134217728, -10458849/67108864 ]
   , ![ -2423385/16777216, 5219167/8589934592, -11362443/536870912, -5433419/8388608, -2452037/134217728 ]
   , ![ -5716417/4194304, -2780951/134217728, 11962611/268435456, 10579229/268435456, 1569829/16777216 ]
   , ![ -6508637/4194304, 11247727/134217728, -9451237/268435456, 6506371/1073741824, 1111865/134217728 ]
   , ![ 10876585/8388608, 3148325/33554432, 11775861/67108864, 8955007/67108864, 10025293/33554432 ]
   , ![ 2129767/134217728, 5532673/16777216, -8903769/33554432, -6948519/67108864, 10280165/134217728 ]
   , ![ -2790769/67108864, -12387793/8388608, -7775555/134217728, -3467297/16777216, 6762795/33554432 ]
   , ![ -11099699/134217728, 10957321/4294967296, 2650035/268435456, 578569/8388608, -14746133/16777216 ]
   , ![ -833749/524288, 12769743/268435456, 16386889/2147483648, -7655833/536870912, 6121359/2147483648 ]
   , ![ 15214277/536870912, -12392269/536870912, -10244987/134217728, -3236367/4194304, 8372401/16777216 ]
   , ![ 9342359/67108864, -9599621/16777216, 14321199/33554432, -692121/2097152, 1178029/4194304 ]
   , ![ 8652077/33554432, -4206397/67108864, -5555473/16777216, 11069775/33554432, -7183291/8388608 ]
   , ![ 9213779/134217728, 10559735/4294967296, -1914079/134217728, 1878357/67108864, -15527565/8388608 ]
   , ![ -12492147/16777216, 6697207/2147483648, -6304173/33554432, 7310947/536870912, -8565775/536870912 ]
   , ![ -1747217/4194304, 12956735/1073741824, -12928147/268435456, -12234047/33554432, 4835093/16777216 ]
   , ![ -10612243/16777216, -9627035/268435456, 7610387/268435456, 9900947/134217728, 545257/8388608 ]
   , ![ 5261429/134217728, 4735109/8388608, 8818709/33554432, -58555/4194304, -12008561/33554432 ]
   , ![ -2589617/67108864, -259791/2097152, -6397379/8388608, 11355813/268435456, 837017/16777216 ]
   , ![ -13223047/8388608, 15118835/34359738368, -4467711/536870912, -12436709/134217728, -5301117/1073741824 ]
   , ![ 10408031/16777216, 10071349/134217728, -7845885/536870912, 8810555/33554432, -8655299/33554432 ] ]
def B0 : Fin 50 → ℚ := ![ 15275991/67108864, -12667603/67108864, 14336977/268435456, -12678911/33554432, -5452803/67108864, -9875925/16777216, 10013515/134217728, -3295775/8388608, -11955545/33554432, -5627481/33554432, 15760087/268435456, 12342461/67108864, 2213871/16777216, -647351/2097152, 13215681/67108864, 6934493/33554432, -5229391/16777216, 8229587/268435456, -9316187/67108864, -11657951/33554432, -4851595/1073741824, -6553449/16777216, 13014221/134217728, 5278869/536870912, -2531145/134217728, -15563821/67108864, -15982983/67108864, 9531445/134217728, -2380905/16777216, -927585/2097152, 9379873/16777216, 4546055/33554432, -3130771/8388608, -27223/65536, 12744611/16777216, 8913735/67108864, 15808567/67108864, 3604719/16777216, -14792169/33554432, -10374601/134217728, 14871727/67108864, -13977391/2147483648, -5325449/8388608, -5161779/33554432, -3845519/67108864, -3665117/33554432, 4970673/134217728, 14444163/268435456, -7508643/16777216, 5902795/33554432 ]
/-- Readout = row 0 of the real layer-1 weights. -/
def Wr : Fin 50 → ℚ := ![ -12361587/67108864, 2307431/67108864, -7727049/67108864, 3099641/16777216, -4601923/33554432, -12704849/67108864, -6280509/8388608, 9661143/16777216, -1787203/134217728, 301237/2097152, 8929975/67108864, -15060437/67108864, 10138405/33554432, 10965293/268435456, -11393709/33554432, 2178253/33554432, 2455151/33554432, -15409235/33554432, 15929765/33554432, 3164401/8388608, -9345497/8388608, -9594101/16777216, 13398983/268435456, -4264869/16777216, -13552769/536870912, 7575517/33554432, 10063779/67108864, -5207715/33554432, -4617439/268435456, 16620953/16777216, 10520563/134217728, -2419241/16777216, -751095/4194304, -2852437/8388608, 14248621/67108864, 554189/67108864, 2296103/33554432, 9864097/16777216, -358009/2097152, -9121605/16777216, 15962783/134217728, -8319033/16777216, -13979783/8388608, -10874119/33554432, -16560213/1073741824, 4279029/8388608, 12628519/134217728, 11320863/33554432, 3319129/8388608, -14997019/67108864 ]
def br : ℚ := 11213891/134217728

def affine5 (Wm : Fin 50 → Fin 5 → ℚ) (b : Fin 50 → ℚ) (x : Fin 5 → ℚ) : Fin 50 → ℚ := fun i => (∑ j : Fin 5, Wm i j * x j) + b i
def affine50 (Wm : Fin 50 → Fin 50 → ℚ) (b : Fin 50 → ℚ) (x : Fin 50 → ℚ) : Fin 50 → ℚ := fun i => (∑ j : Fin 50, Wm i j * x j) + b i
def reluV (z : Fin 50 → ℚ) : Fin 50 → ℚ := fun i => relu (z i)
def z0lay (x : Fin 5 → ℚ) : Fin 50 → ℚ := affine5 W0 B0 x
def a0lay (x : Fin 5 → ℚ) : Fin 50 → ℚ := reluV (z0lay x)
/-- The real readout, summing over ALL 50 layer-0 activations. -/
def netEvalWide (x : Fin 5 → ℚ) : ℚ := (∑ j : Fin 50, Wr j * a0lay x j) + br

def uz0 : Fin 50 → ℚ := ![ 14760595147/8589934592, 0, 3023736455/8589934592, 0, 159834351/536870912, 7325652217/8589934592, 174136733/268435456, 0, 0, 0, 122747677/134217728, 612864466753/549755813888, 7560059821/17179869184, 0, 10084391141/17179869184, 11549037131/8589934592, 0, 6009801547/4294967296, 3186811173/8589934592, 0, 40474388605/34359738368, 0, 18792838575/8589934592, 4087723105/4294967296, 0, 0, 0, 784770183/1073741824, 626696549/536870912, 0, 26755925891/17179869184, 0, 0, 0, 7384617211/4294967296, 6203328525/17179869184, 3420631781/4294967296, 5548422823/8589934592, 0, 0, 584941743/1073741824, 2063260669/2147483648, 3094284891/8589934592, 0, 0, 0, 1396622539/2147483648, 126992671/268435456, 0, 974427749/1073741824 ]
def lzz0 : Fin 50 → ℚ := ![ -9437149291/8589934592, -27777588871/34359738368, -311884855/536870912, -51854767767/34359738368, -2366066067/4294967296, -75282198781/34359738368, 1385239849/4294967296, -47669699023/34359738368, -3295039015/2147483648, -262113220535/274877906944, 4005036029/17179869184, 2774107701/4294967296, -1571375941/8589934592, -845777495/1073741824, -1816645003/4294967296, -8627158993/8589934592, -260119613/268435456, -40472059013/34359738368, -3849035413/8589934592, -21925678755/17179869184, -11411339427/8589934592, -7285987031/8589934592, -132685779119/68719476736, -321765329/1073741824, -3190954945/137438953472, -567743245/536870912, -18374697687/17179869184, 1736985499/4294967296, -41782962645/34359738368, -1087501295/2147483648, 12001325243/8589934592, -2494778041/8589934592, -47144556235/34359738368, -212094107861/137438953472, 11208761703/8589934592, -1053913995/4294967296, -820840583/1073741824, 4929817279/8589934592, -1686090381/1073741824, -12807582065/17179869184, -1075195403/2147483648, 2052665345/4294967296, 125793097/536870912, -25703432327/34359738368, -1503681771/2147483648, -9893145669/17179869184, -107881097/536870912, -14502556451/34359738368, -217122740881/137438953472, 1570303513/2147483648 ]
def uzz0 : Fin 50 → ℚ := ![ 14760595147/8589934592, -694263215/1073741824, 3023736455/8589934592, -2823208859/2147483648, 159834351/536870912, 7325652217/8589934592, 174136733/268435456, -149486367/134217728, -22813466453/17179869184, -3494272251/4294967296, 122747677/134217728, 612864466753/549755813888, 7560059821/17179869184, -153847115/4294967296, 10084391141/17179869184, 11549037131/8589934592, -457616217/2147483648, 6009801547/4294967296, 3186811173/8589934592, -29634471639/34359738368, 40474388605/34359738368, -1128458125/2147483648, 18792838575/8589934592, 4087723105/4294967296, -11086728039/1099511627776, -23228051331/34359738368, -6106292087/8589934592, 784770183/1073741824, 626696549/536870912, -758950103/2147483648, 26755925891/17179869184, -3757167425/17179869184, -2516333429/2147483648, -21954382521/17179869184, 7384617211/4294967296, 6203328525/17179869184, 3420631781/4294967296, 5548422823/8589934592, -375227755227/274877906944, -4930113813/8589934592, 584941743/1073741824, 2063260669/2147483648, 3094284891/8589934592, -2085842889/4294967296, -2427623787/4294967296, -477549995/1073741824, 1396622539/2147483648, 126992671/268435456, -97437183905/68719476736, 974427749/1073741824 ]

def inBox (x : Fin 5 → ℚ) : Prop :=
  (19/32 ≤ x 0 ∧ x 0 ≤ 11/16) ∧ (-1/2 ≤ x 1 ∧ x 1 ≤ 1/2) ∧
  (-1/2 ≤ x 2 ∧ x 2 ≤ 1/2) ∧ (57/128 ≤ x 3 ∧ x 3 ≤ 1/2) ∧ (-1/2 ≤ x 4 ∧ x 4 ≤ -57/128)

theorem z0_0 (x : Fin 5 → ℚ) : z0lay x 0 = (14497179/268435456)*x 0 + (-684437/262144)*x 1 + (-12081407/67108864)*x 2 + (4063341/16777216)*x 3 + (9489663/67108864)*x 4 + (15275991/67108864) := by
  show (∑ j : Fin 5, W0 0 j * x j) + B0 0 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_1 (x : Fin 5 → ℚ) : z0lay x 1 = (-4713307/4194304)*x 0 + (14152937/536870912)*x 1 + (-2464047/268435456)*x 2 + (14931185/268435456)*x 3 + (-5496803/16777216)*x 4 + (-12667603/67108864) := by
  show (∑ j : Fin 5, W0 1 j * x j) + B0 1 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_2 (x : Fin 5 → ℚ) : z0lay x 2 = (3288653/16777216)*x 0 + (16251015/67108864)*x 1 + (10711447/16777216)*x 2 + (-8023955/16777216)*x 3 + (9568181/67108864)*x 4 + (14336977/268435456) := by
  show (∑ j : Fin 5, W0 2 j * x j) + B0 2 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_3 (x : Fin 5 → ℚ) : z0lay x 3 = (-13674689/8388608)*x 0 + (-9246179/268435456)*x 1 + (-6501421/1073741824)*x 2 + (12034069/1073741824)*x 3 + (-11273967/1073741824)*x 4 + (-12678911/33554432) := by
  show (∑ j : Fin 5, W0 3 j * x j) + B0 3 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_4 (x : Fin 5 → ℚ) : z0lay x 4 = (-5958143/16777216)*x 0 + (1186923/2097152)*x 1 + (15318739/67108864)*x 2 + (2975305/16777216)*x 3 + (-6981939/33554432)*x 4 + (-5452803/67108864) := by
  show (∑ j : Fin 5, W0 4 j * x j) + B0 4 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_5 (x : Fin 5 → ℚ) : z0lay x 5 = (-9178291/268435456)*x 0 + (12546841/8388608)*x 1 + (-3216423/2097152)*x 2 + (10873059/268435456)*x 3 + (5514671/33554432)*x 4 + (-9875925/16777216) := by
  show (∑ j : Fin 5, W0 5 j * x j) + B0 5 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_6 (x : Fin 5 → ℚ) : z0lay x 6 = (13488949/33554432)*x 0 + (7516931/33554432)*x 1 + (-12540231/268435456)*x 2 + (1374809/8388608)*x 3 + (-5396425/33554432)*x 4 + (10013515/134217728) := by
  show (∑ j : Fin 5, W0 6 j * x j) + B0 6 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_7 (x : Fin 5 → ℚ) : z0lay x 7 = (-2969043/2097152)*x 0 + (-5015911/67108864)*x 1 + (16223863/268435456)*x 2 + (6478099/134217728)*x 3 + (-15034963/268435456)*x 4 + (-3295775/8388608) := by
  show (∑ j : Fin 5, W0 7 j * x j) + B0 7 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_8 (x : Fin 5 → ℚ) : z0lay x 8 = (-12121371/8388608)*x 0 + (6018363/134217728)*x 1 + (9544663/1073741824)*x 2 + (-4198163/16777216)*x 3 + (8768605/134217728)*x 4 + (-11955545/33554432) := by
  show (∑ j : Fin 5, W0 8 j * x j) + B0 8 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_9 (x : Fin 5 → ℚ) : z0lay x 9 = (-9457317/8388608)*x 0 + (6439525/268435456)*x 1 + (-5136303/536870912)*x 2 + (2396581/268435456)*x 3 + (-9835625/2147483648)*x 4 + (-5627481/33554432) := by
  show (∑ j : Fin 5, W0 9 j * x j) + B0 9 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_10 (x : Fin 5 → ℚ) : z0lay x 10 = (10296463/16777216)*x 0 + (-9358667/16777216)*x 1 + (-6972705/134217728)*x 2 + (10794595/67108864)*x 3 + (-13042943/134217728)*x 4 + (15760087/268435456) := by
  show (∑ j : Fin 5, W0 10 j * x j) + B0 10 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_11 (x : Fin 5 → ℚ) : z0lay x 11 = (7832435/8388608)*x 0 + (13666519/67108864)*x 1 + (11152017/67108864)*x 2 + (-6535351/4294967296)*x 3 + (-14055817/67108864)*x 4 + (12342461/67108864) := by
  show (∑ j : Fin 5, W0 11 j * x j) + B0 11 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_12 (x : Fin 5 → ℚ) : z0lay x 12 = (-10952865/268435456)*x 0 + (287659/524288)*x 1 + (15431495/268435456)*x 2 + (9595561/67108864)*x 3 + (12732981/134217728)*x 4 + (2213871/16777216) := by
  show (∑ j : Fin 5, W0 12 j * x j) + B0 12 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_13 (x : Fin 5 → ℚ) : z0lay x 13 = (-14244863/67108864)*x 0 + (-5502977/16777216)*x 1 + (11996917/33554432)*x 2 + (-13076665/33554432)*x 3 + (-1926599/4194304)*x 4 + (-647351/2097152) := by
  show (∑ j : Fin 5, W0 13 j * x j) + B0 13 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_14 (x : Fin 5 → ℚ) : z0lay x 14 = (4297383/134217728)*x 0 + (7087619/16777216)*x 1 + (-4771717/8388608)*x 2 + (-14145341/67108864)*x 3 + (10167073/134217728)*x 4 + (13215681/67108864) := by
  show (∑ j : Fin 5, W0 14 j * x j) + B0 14 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_15 (x : Fin 5 → ℚ) : z0lay x 15 = (-832519/67108864)*x 0 + (9582013/4194304)*x 1 + (1793877/33554432)*x 2 + (3896079/67108864)*x 3 + (7962601/67108864)*x 4 + (6934493/33554432) := by
  show (∑ j : Fin 5, W0 15 j * x j) + B0 15 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_16 (x : Fin 5 → ℚ) : z0lay x 16 = (-4108069/33554432)*x 0 + (-5973041/8388608)*x 1 + (2458611/268435456)*x 2 + (-6561955/16777216)*x 3 + (142543/4194304)*x 4 + (-5229391/16777216) := by
  show (∑ j : Fin 5, W0 16 j * x j) + B0 16 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_17 (x : Fin 5 → ℚ) : z0lay x 17 = (16152889/268435456)*x 0 + (-8577479/134217728)*x 1 + (-5248773/2097152)*x 2 + (13413773/268435456)*x 3 + (-5072061/134217728)*x 4 + (8229587/268435456) := by
  show (∑ j : Fin 5, W0 17 j * x j) + B0 17 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_18 (x : Fin 5 → ℚ) : z0lay x 18 = (11180793/134217728)*x 0 + (-10938369/268435456)*x 1 + (-12618161/16777216)*x 2 + (-7972399/67108864)*x 3 + (-14632685/67108864)*x 4 + (-9316187/67108864) := by
  show (∑ j : Fin 5, W0 18 j * x j) + B0 18 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_19 (x : Fin 5 → ℚ) : z0lay x 19 = (-4983001/4194304)*x 0 + (9705955/67108864)*x 1 + (-10018011/67108864)*x 2 + (-9684239/268435456)*x 3 + (-15962917/134217728)*x 4 + (-11657951/33554432) := by
  show (∑ j : Fin 5, W0 19 j * x j) + B0 19 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_20 (x : Fin 5 → ℚ) : z0lay x 20 = (-13896501/134217728)*x 0 + (2348525/33554432)*x 1 + (2541465/1048576)*x 2 + (1520009/67108864)*x 3 + (8579331/268435456)*x 4 + (-4851595/1073741824) := by
  show (∑ j : Fin 5, W0 20 j * x j) + B0 20 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_21 (x : Fin 5 → ℚ) : z0lay x 21 = (-2865223/33554432)*x 0 + (734905/4194304)*x 1 + (-5865375/67108864)*x 2 + (-12278171/16777216)*x 3 + (-14820993/67108864)*x 4 + (-6553449/16777216) := by
  show (∑ j : Fin 5, W0 21 j * x j) + B0 21 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_22 (x : Fin 5 → ℚ) : z0lay x 22 = (-5203299/268435456)*x 0 + (16751631/4194304)*x 1 + (3952947/33554432)*x 2 + (10524629/134217728)*x 3 + (-7794453/536870912)*x 4 + (13014221/134217728) := by
  show (∑ j : Fin 5, W0 22 j * x j) + B0 22 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_23 (x : Fin 5 → ℚ) : z0lay x 23 = (4479275/268435456)*x 0 + (-5489547/8388608)*x 1 + (2349213/4194304)*x 2 + (13192193/67108864)*x 3 + (-15092951/33554432)*x 4 + (5278869/536870912) := by
  show (∑ j : Fin 5, W0 23 j * x j) + B0 23 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_24 (x : Fin 5 → ℚ) : z0lay x 24 = (900005/536870912)*x 0 + (5781391/1073741824)*x 1 + (-7802227/1073741824)*x 2 + (4489143/1073741824)*x 3 + (15299103/8589934592)*x 4 + (-2531145/134217728) := by
  show (∑ j : Fin 5, W0 24 j * x j) + B0 24 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_25 (x : Fin 5 → ℚ) : z0lay x 25 = (-15057971/16777216)*x 0 + (-4281747/33554432)*x 1 + (2731381/16777216)*x 2 + (-12916685/268435456)*x 3 + (10542279/134217728)*x 4 + (-15563821/67108864) := by
  show (∑ j : Fin 5, W0 25 j * x j) + B0 25 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_26 (x : Fin 5 → ℚ) : z0lay x 26 = (-7828417/8388608)*x 0 + (-6530417/268435456)*x 1 + (15453359/67108864)*x 2 + (-14027967/67108864)*x 3 + (-12665617/134217728)*x 4 + (-15982983/67108864) := by
  show (∑ j : Fin 5, W0 26 j * x j) + B0 26 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_27 (x : Fin 5 → ℚ) : z0lay x 27 = (10759765/67108864)*x 0 + (247827/67108864)*x 1 + (8796261/33554432)*x 2 + (9460437/33554432)*x 3 + (-1156529/2097152)*x 4 + (9531445/134217728) := by
  show (∑ j : Fin 5, W0 27 j * x j) + B0 27 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_28 (x : Fin 5 → ℚ) : z0lay x 28 = (1399255/16777216)*x 0 + (8442337/4194304)*x 1 + (11922225/33554432)*x 2 + (9665421/268435456)*x 3 + (-13374555/134217728)*x 4 + (-2380905/16777216) := by
  show (∑ j : Fin 5, W0 28 j * x j) + B0 28 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_29 (x : Fin 5 → ℚ) : z0lay x 29 = (595631/2097152)*x 0 + (-3125535/67108864)*x 1 + (8030837/1073741824)*x 2 + (-3525367/4194304)*x 3 + (-4041539/8388608)*x 4 + (-927585/2097152) := by
  show (∑ j : Fin 5, W0 29 j * x j) + B0 29 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_30 (x : Fin 5 → ℚ) : z0lay x 30 = (11517139/8388608)*x 0 + (12630425/2147483648)*x 1 + (14056139/1073741824)*x 2 + (-9945601/134217728)*x 3 + (-10458849/67108864)*x 4 + (9379873/16777216) := by
  show (∑ j : Fin 5, W0 30 j * x j) + B0 30 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_31 (x : Fin 5 → ℚ) : z0lay x 31 = (-2423385/16777216)*x 0 + (5219167/8589934592)*x 1 + (-11362443/536870912)*x 2 + (-5433419/8388608)*x 3 + (-2452037/134217728)*x 4 + (4546055/33554432) := by
  show (∑ j : Fin 5, W0 31 j * x j) + B0 31 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_32 (x : Fin 5 → ℚ) : z0lay x 32 = (-5716417/4194304)*x 0 + (-2780951/134217728)*x 1 + (11962611/268435456)*x 2 + (10579229/268435456)*x 3 + (1569829/16777216)*x 4 + (-3130771/8388608) := by
  show (∑ j : Fin 5, W0 32 j * x j) + B0 32 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_33 (x : Fin 5 → ℚ) : z0lay x 33 = (-6508637/4194304)*x 0 + (11247727/134217728)*x 1 + (-9451237/268435456)*x 2 + (6506371/1073741824)*x 3 + (1111865/134217728)*x 4 + (-27223/65536) := by
  show (∑ j : Fin 5, W0 33 j * x j) + B0 33 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_34 (x : Fin 5 → ℚ) : z0lay x 34 = (10876585/8388608)*x 0 + (3148325/33554432)*x 1 + (11775861/67108864)*x 2 + (8955007/67108864)*x 3 + (10025293/33554432)*x 4 + (12744611/16777216) := by
  show (∑ j : Fin 5, W0 34 j * x j) + B0 34 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_35 (x : Fin 5 → ℚ) : z0lay x 35 = (2129767/134217728)*x 0 + (5532673/16777216)*x 1 + (-8903769/33554432)*x 2 + (-6948519/67108864)*x 3 + (10280165/134217728)*x 4 + (8913735/67108864) := by
  show (∑ j : Fin 5, W0 35 j * x j) + B0 35 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_36 (x : Fin 5 → ℚ) : z0lay x 36 = (-2790769/67108864)*x 0 + (-12387793/8388608)*x 1 + (-7775555/134217728)*x 2 + (-3467297/16777216)*x 3 + (6762795/33554432)*x 4 + (15808567/67108864) := by
  show (∑ j : Fin 5, W0 36 j * x j) + B0 36 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_37 (x : Fin 5 → ℚ) : z0lay x 37 = (-11099699/134217728)*x 0 + (10957321/4294967296)*x 1 + (2650035/268435456)*x 2 + (578569/8388608)*x 3 + (-14746133/16777216)*x 4 + (3604719/16777216) := by
  show (∑ j : Fin 5, W0 37 j * x j) + B0 37 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_38 (x : Fin 5 → ℚ) : z0lay x 38 = (-833749/524288)*x 0 + (12769743/268435456)*x 1 + (16386889/2147483648)*x 2 + (-7655833/536870912)*x 3 + (6121359/2147483648)*x 4 + (-14792169/33554432) := by
  show (∑ j : Fin 5, W0 38 j * x j) + B0 38 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_39 (x : Fin 5 → ℚ) : z0lay x 39 = (15214277/536870912)*x 0 + (-12392269/536870912)*x 1 + (-10244987/134217728)*x 2 + (-3236367/4194304)*x 3 + (8372401/16777216)*x 4 + (-10374601/134217728) := by
  show (∑ j : Fin 5, W0 39 j * x j) + B0 39 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_40 (x : Fin 5 → ℚ) : z0lay x 40 = (9342359/67108864)*x 0 + (-9599621/16777216)*x 1 + (14321199/33554432)*x 2 + (-692121/2097152)*x 3 + (1178029/4194304)*x 4 + (14871727/67108864) := by
  show (∑ j : Fin 5, W0 40 j * x j) + B0 40 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_41 (x : Fin 5 → ℚ) : z0lay x 41 = (8652077/33554432)*x 0 + (-4206397/67108864)*x 1 + (-5555473/16777216)*x 2 + (11069775/33554432)*x 3 + (-7183291/8388608)*x 4 + (-13977391/2147483648) := by
  show (∑ j : Fin 5, W0 41 j * x j) + B0 41 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_42 (x : Fin 5 → ℚ) : z0lay x 42 = (9213779/134217728)*x 0 + (10559735/4294967296)*x 1 + (-1914079/134217728)*x 2 + (1878357/67108864)*x 3 + (-15527565/8388608)*x 4 + (-5325449/8388608) := by
  show (∑ j : Fin 5, W0 42 j * x j) + B0 42 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_43 (x : Fin 5 → ℚ) : z0lay x 43 = (-12492147/16777216)*x 0 + (6697207/2147483648)*x 1 + (-6304173/33554432)*x 2 + (7310947/536870912)*x 3 + (-8565775/536870912)*x 4 + (-5161779/33554432) := by
  show (∑ j : Fin 5, W0 43 j * x j) + B0 43 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_44 (x : Fin 5 → ℚ) : z0lay x 44 = (-1747217/4194304)*x 0 + (12956735/1073741824)*x 1 + (-12928147/268435456)*x 2 + (-12234047/33554432)*x 3 + (4835093/16777216)*x 4 + (-3845519/67108864) := by
  show (∑ j : Fin 5, W0 44 j * x j) + B0 44 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_45 (x : Fin 5 → ℚ) : z0lay x 45 = (-10612243/16777216)*x 0 + (-9627035/268435456)*x 1 + (7610387/268435456)*x 2 + (9900947/134217728)*x 3 + (545257/8388608)*x 4 + (-3665117/33554432) := by
  show (∑ j : Fin 5, W0 45 j * x j) + B0 45 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_46 (x : Fin 5 → ℚ) : z0lay x 46 = (5261429/134217728)*x 0 + (4735109/8388608)*x 1 + (8818709/33554432)*x 2 + (-58555/4194304)*x 3 + (-12008561/33554432)*x 4 + (4970673/134217728) := by
  show (∑ j : Fin 5, W0 46 j * x j) + B0 46 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_47 (x : Fin 5 → ℚ) : z0lay x 47 = (-2589617/67108864)*x 0 + (-259791/2097152)*x 1 + (-6397379/8388608)*x 2 + (11355813/268435456)*x 3 + (837017/16777216)*x 4 + (14444163/268435456) := by
  show (∑ j : Fin 5, W0 47 j * x j) + B0 47 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_48 (x : Fin 5 → ℚ) : z0lay x 48 = (-13223047/8388608)*x 0 + (15118835/34359738368)*x 1 + (-4467711/536870912)*x 2 + (-12436709/134217728)*x 3 + (-5301117/1073741824)*x 4 + (-7508643/16777216) := by
  show (∑ j : Fin 5, W0 48 j * x j) + B0 48 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0_49 (x : Fin 5 → ℚ) : z0lay x 49 = (10408031/16777216)*x 0 + (10071349/134217728)*x 1 + (-7845885/536870912)*x 2 + (8810555/33554432)*x 3 + (-8655299/33554432)*x 4 + (5902795/33554432) := by
  show (∑ j : Fin 5, W0 49 j * x j) + B0 49 = _
  simp [Fin.sum_univ_succ, W0, B0]; ring
theorem z0box_0 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 0 ≤ z0lay x 0 ∧ z0lay x 0 ≤ uzz0 0 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_0]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (14497179/268435456)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (14497179/268435456)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-684437/262144:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-684437/262144:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12081407/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12081407/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (4063341/16777216)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (4063341/16777216)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (9489663/67108864)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (9489663/67108864))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (14497179/268435456)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (14497179/268435456)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-684437/262144:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-684437/262144:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12081407/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12081407/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (4063341/16777216)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (4063341/16777216)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (9489663/67108864)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (9489663/67108864))]
theorem z0box_1 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 1 ≤ z0lay x 1 ∧ z0lay x 1 ≤ uzz0 1 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_1]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-4713307/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-4713307/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (14152937/536870912)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (14152937/536870912)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-2464047/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-2464047/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (14931185/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (14931185/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5496803/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5496803/16777216:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-4713307/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-4713307/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (14152937/536870912)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (14152937/536870912)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-2464047/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-2464047/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (14931185/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (14931185/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5496803/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5496803/16777216:ℚ) ≤ 0)]
theorem z0box_2 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 2 ≤ z0lay x 2 ∧ z0lay x 2 ≤ uzz0 2 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_2]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (3288653/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (3288653/16777216)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (16251015/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (16251015/67108864)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (10711447/16777216)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (10711447/16777216)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-8023955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-8023955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (9568181/67108864)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (9568181/67108864))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (3288653/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (3288653/16777216)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (16251015/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (16251015/67108864)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (10711447/16777216)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (10711447/16777216)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-8023955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-8023955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (9568181/67108864)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (9568181/67108864))]
theorem z0box_3 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 3 ≤ z0lay x 3 ∧ z0lay x 3 ≤ uzz0 3 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_3]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-13674689/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-13674689/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9246179/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9246179/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6501421/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6501421/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (12034069/1073741824)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (12034069/1073741824)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-11273967/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-11273967/1073741824:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-13674689/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-13674689/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9246179/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9246179/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6501421/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6501421/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (12034069/1073741824)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (12034069/1073741824)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-11273967/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-11273967/1073741824:ℚ) ≤ 0)]
theorem z0box_4 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 4 ≤ z0lay x 4 ∧ z0lay x 4 ≤ uzz0 4 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_4]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-5958143/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-5958143/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (1186923/2097152)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (1186923/2097152)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (15318739/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (15318739/67108864)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (2975305/16777216)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (2975305/16777216)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-6981939/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-6981939/33554432:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-5958143/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-5958143/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (1186923/2097152)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (1186923/2097152)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (15318739/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (15318739/67108864)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (2975305/16777216)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (2975305/16777216)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-6981939/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-6981939/33554432:ℚ) ≤ 0)]
theorem z0box_5 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 5 ≤ z0lay x 5 ∧ z0lay x 5 ≤ uzz0 5 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_5]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-9178291/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-9178291/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12546841/8388608)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12546841/8388608)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-3216423/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-3216423/2097152:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10873059/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10873059/268435456)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (5514671/33554432)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (5514671/33554432))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-9178291/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-9178291/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12546841/8388608)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12546841/8388608)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-3216423/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-3216423/2097152:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10873059/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10873059/268435456)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (5514671/33554432)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (5514671/33554432))]
theorem z0box_6 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 6 ≤ z0lay x 6 ∧ z0lay x 6 ≤ uzz0 6 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_6]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (13488949/33554432)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (13488949/33554432)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (7516931/33554432)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (7516931/33554432)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12540231/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12540231/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (1374809/8388608)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (1374809/8388608)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5396425/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5396425/33554432:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (13488949/33554432)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (13488949/33554432)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (7516931/33554432)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (7516931/33554432)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12540231/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12540231/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (1374809/8388608)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (1374809/8388608)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5396425/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5396425/33554432:ℚ) ≤ 0)]
theorem z0box_7 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 7 ≤ z0lay x 7 ∧ z0lay x 7 ≤ uzz0 7 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_7]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2969043/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2969043/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5015911/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5015911/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (16223863/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (16223863/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (6478099/134217728)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (6478099/134217728)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15034963/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15034963/268435456:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2969043/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2969043/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5015911/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5015911/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (16223863/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (16223863/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (6478099/134217728)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (6478099/134217728)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15034963/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15034963/268435456:ℚ) ≤ 0)]
theorem z0box_8 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 8 ≤ z0lay x 8 ∧ z0lay x 8 ≤ uzz0 8 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_8]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-12121371/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-12121371/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (6018363/134217728)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (6018363/134217728)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (9544663/1073741824)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (9544663/1073741824)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-4198163/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-4198163/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (8768605/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (8768605/134217728))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-12121371/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-12121371/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (6018363/134217728)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (6018363/134217728)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (9544663/1073741824)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (9544663/1073741824)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-4198163/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-4198163/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (8768605/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (8768605/134217728))]
theorem z0box_9 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 9 ≤ z0lay x 9 ∧ z0lay x 9 ≤ uzz0 9 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_9]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-9457317/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-9457317/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (6439525/268435456)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (6439525/268435456)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5136303/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5136303/536870912:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (2396581/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (2396581/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-9835625/2147483648:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-9835625/2147483648:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-9457317/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-9457317/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (6439525/268435456)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (6439525/268435456)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5136303/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5136303/536870912:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (2396581/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (2396581/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-9835625/2147483648:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-9835625/2147483648:ℚ) ≤ 0)]
theorem z0box_10 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 10 ≤ z0lay x 10 ∧ z0lay x 10 ≤ uzz0 10 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_10]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10296463/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10296463/16777216)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9358667/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9358667/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6972705/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6972705/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10794595/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10794595/67108864)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-13042943/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-13042943/134217728:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10296463/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10296463/16777216)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9358667/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9358667/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6972705/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6972705/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10794595/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10794595/67108864)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-13042943/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-13042943/134217728:ℚ) ≤ 0)]
theorem z0box_11 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 11 ≤ z0lay x 11 ∧ z0lay x 11 ≤ uzz0 11 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_11]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (7832435/8388608)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (7832435/8388608)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (13666519/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (13666519/67108864)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11152017/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11152017/67108864)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-6535351/4294967296:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-6535351/4294967296:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14055817/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14055817/67108864:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (7832435/8388608)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (7832435/8388608)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (13666519/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (13666519/67108864)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11152017/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11152017/67108864)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-6535351/4294967296:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-6535351/4294967296:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14055817/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14055817/67108864:ℚ) ≤ 0)]
theorem z0box_12 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 12 ≤ z0lay x 12 ∧ z0lay x 12 ≤ uzz0 12 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_12]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-10952865/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-10952865/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (287659/524288)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (287659/524288)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (15431495/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (15431495/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9595561/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9595561/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (12732981/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (12732981/134217728))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-10952865/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-10952865/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (287659/524288)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (287659/524288)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (15431495/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (15431495/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9595561/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9595561/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (12732981/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (12732981/134217728))]
theorem z0box_13 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 13 ≤ z0lay x 13 ∧ z0lay x 13 ≤ uzz0 13 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_13]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-14244863/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-14244863/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5502977/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5502977/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11996917/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11996917/33554432)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-13076665/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-13076665/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-1926599/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-1926599/4194304:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-14244863/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-14244863/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5502977/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5502977/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11996917/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11996917/33554432)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-13076665/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-13076665/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-1926599/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-1926599/4194304:ℚ) ≤ 0)]
theorem z0box_14 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 14 ≤ z0lay x 14 ∧ z0lay x 14 ≤ uzz0 14 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_14]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (4297383/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (4297383/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (7087619/16777216)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (7087619/16777216)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-4771717/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-4771717/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-14145341/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-14145341/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10167073/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10167073/134217728))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (4297383/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (4297383/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (7087619/16777216)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (7087619/16777216)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-4771717/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-4771717/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-14145341/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-14145341/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10167073/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10167073/134217728))]
theorem z0box_15 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 15 ≤ z0lay x 15 ∧ z0lay x 15 ≤ uzz0 15 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_15]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-832519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-832519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (9582013/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (9582013/4194304)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (1793877/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (1793877/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (3896079/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (3896079/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (7962601/67108864)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (7962601/67108864))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-832519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-832519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (9582013/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (9582013/4194304)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (1793877/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (1793877/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (3896079/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (3896079/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (7962601/67108864)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (7962601/67108864))]
theorem z0box_16 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 16 ≤ z0lay x 16 ∧ z0lay x 16 ≤ uzz0 16 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_16]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-4108069/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-4108069/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5973041/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5973041/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2458611/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2458611/268435456)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-6561955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-6561955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (142543/4194304)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (142543/4194304))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-4108069/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-4108069/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5973041/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5973041/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2458611/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2458611/268435456)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-6561955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-6561955/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (142543/4194304)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (142543/4194304))]
theorem z0box_17 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 17 ≤ z0lay x 17 ∧ z0lay x 17 ≤ uzz0 17 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_17]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (16152889/268435456)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (16152889/268435456)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-8577479/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-8577479/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5248773/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5248773/2097152:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (13413773/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (13413773/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5072061/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5072061/134217728:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (16152889/268435456)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (16152889/268435456)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-8577479/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-8577479/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5248773/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5248773/2097152:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (13413773/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (13413773/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5072061/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5072061/134217728:ℚ) ≤ 0)]
theorem z0box_18 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 18 ≤ z0lay x 18 ∧ z0lay x 18 ≤ uzz0 18 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_18]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (11180793/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (11180793/134217728)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-10938369/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-10938369/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12618161/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12618161/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-7972399/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-7972399/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14632685/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14632685/67108864:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (11180793/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (11180793/134217728)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-10938369/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-10938369/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12618161/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12618161/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-7972399/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-7972399/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14632685/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14632685/67108864:ℚ) ≤ 0)]
theorem z0box_19 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 19 ≤ z0lay x 19 ∧ z0lay x 19 ≤ uzz0 19 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_19]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-4983001/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-4983001/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (9705955/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (9705955/67108864)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-10018011/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-10018011/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-9684239/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-9684239/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15962917/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15962917/134217728:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-4983001/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-4983001/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (9705955/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (9705955/67108864)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-10018011/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-10018011/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-9684239/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-9684239/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15962917/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15962917/134217728:ℚ) ≤ 0)]
theorem z0box_20 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 20 ≤ z0lay x 20 ∧ z0lay x 20 ≤ uzz0 20 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_20]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-13896501/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-13896501/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (2348525/33554432)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (2348525/33554432)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2541465/1048576)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2541465/1048576)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (1520009/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (1520009/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (8579331/268435456)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (8579331/268435456))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-13896501/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-13896501/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (2348525/33554432)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (2348525/33554432)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2541465/1048576)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2541465/1048576)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (1520009/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (1520009/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (8579331/268435456)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (8579331/268435456))]
theorem z0box_21 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 21 ≤ z0lay x 21 ∧ z0lay x 21 ≤ uzz0 21 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_21]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2865223/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2865223/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (734905/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (734905/4194304)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5865375/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5865375/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12278171/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12278171/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14820993/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14820993/67108864:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2865223/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2865223/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (734905/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (734905/4194304)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5865375/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5865375/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12278171/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12278171/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14820993/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14820993/67108864:ℚ) ≤ 0)]
theorem z0box_22 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 22 ≤ z0lay x 22 ∧ z0lay x 22 ≤ uzz0 22 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_22]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-5203299/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-5203299/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (16751631/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (16751631/4194304)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (3952947/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (3952947/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10524629/134217728)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10524629/134217728)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-7794453/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-7794453/536870912:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-5203299/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-5203299/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (16751631/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (16751631/4194304)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (3952947/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (3952947/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10524629/134217728)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10524629/134217728)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-7794453/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-7794453/536870912:ℚ) ≤ 0)]
theorem z0box_23 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 23 ≤ z0lay x 23 ∧ z0lay x 23 ≤ uzz0 23 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_23]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (4479275/268435456)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (4479275/268435456)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5489547/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5489547/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2349213/4194304)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2349213/4194304)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (13192193/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (13192193/67108864)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15092951/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15092951/33554432:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (4479275/268435456)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (4479275/268435456)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-5489547/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-5489547/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2349213/4194304)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2349213/4194304)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (13192193/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (13192193/67108864)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15092951/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15092951/33554432:ℚ) ≤ 0)]
theorem z0box_24 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 24 ≤ z0lay x 24 ∧ z0lay x 24 ≤ uzz0 24 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_24]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (900005/536870912)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (900005/536870912)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (5781391/1073741824)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (5781391/1073741824)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-7802227/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-7802227/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (4489143/1073741824)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (4489143/1073741824)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (15299103/8589934592)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (15299103/8589934592))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (900005/536870912)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (900005/536870912)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (5781391/1073741824)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (5781391/1073741824)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-7802227/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-7802227/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (4489143/1073741824)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (4489143/1073741824)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (15299103/8589934592)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (15299103/8589934592))]
theorem z0box_25 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 25 ≤ z0lay x 25 ∧ z0lay x 25 ≤ uzz0 25 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_25]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-15057971/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-15057971/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-4281747/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-4281747/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2731381/16777216)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2731381/16777216)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12916685/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12916685/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10542279/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10542279/134217728))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-15057971/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-15057971/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-4281747/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-4281747/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2731381/16777216)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2731381/16777216)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12916685/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12916685/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10542279/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10542279/134217728))]
theorem z0box_26 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 26 ≤ z0lay x 26 ∧ z0lay x 26 ≤ uzz0 26 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_26]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-7828417/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-7828417/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-6530417/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-6530417/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (15453359/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (15453359/67108864)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-14027967/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-14027967/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-12665617/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-12665617/134217728:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-7828417/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-7828417/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-6530417/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-6530417/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (15453359/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (15453359/67108864)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-14027967/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-14027967/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-12665617/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-12665617/134217728:ℚ) ≤ 0)]
theorem z0box_27 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 27 ≤ z0lay x 27 ∧ z0lay x 27 ≤ uzz0 27 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_27]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10759765/67108864)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10759765/67108864)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (247827/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (247827/67108864)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (8796261/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (8796261/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9460437/33554432)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9460437/33554432)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-1156529/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-1156529/2097152:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10759765/67108864)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10759765/67108864)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (247827/67108864)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (247827/67108864)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (8796261/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (8796261/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9460437/33554432)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9460437/33554432)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-1156529/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-1156529/2097152:ℚ) ≤ 0)]
theorem z0box_28 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 28 ≤ z0lay x 28 ∧ z0lay x 28 ≤ uzz0 28 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_28]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (1399255/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (1399255/16777216)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (8442337/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (8442337/4194304)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11922225/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11922225/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9665421/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9665421/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-13374555/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-13374555/134217728:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (1399255/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (1399255/16777216)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (8442337/4194304)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (8442337/4194304)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11922225/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11922225/33554432)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9665421/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9665421/268435456)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-13374555/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-13374555/134217728:ℚ) ≤ 0)]
theorem z0box_29 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 29 ≤ z0lay x 29 ∧ z0lay x 29 ≤ uzz0 29 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_29]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (595631/2097152)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (595631/2097152)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-3125535/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-3125535/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (8030837/1073741824)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (8030837/1073741824)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-3525367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-3525367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-4041539/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-4041539/8388608:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (595631/2097152)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (595631/2097152)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-3125535/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-3125535/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (8030837/1073741824)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (8030837/1073741824)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-3525367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-3525367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-4041539/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-4041539/8388608:ℚ) ≤ 0)]
theorem z0box_30 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 30 ≤ z0lay x 30 ∧ z0lay x 30 ≤ uzz0 30 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_30]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (11517139/8388608)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (11517139/8388608)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12630425/2147483648)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12630425/2147483648)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (14056139/1073741824)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (14056139/1073741824)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-9945601/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-9945601/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-10458849/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-10458849/67108864:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (11517139/8388608)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (11517139/8388608)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12630425/2147483648)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12630425/2147483648)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (14056139/1073741824)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (14056139/1073741824)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-9945601/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-9945601/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-10458849/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-10458849/67108864:ℚ) ≤ 0)]
theorem z0box_31 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 31 ≤ z0lay x 31 ∧ z0lay x 31 ≤ uzz0 31 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_31]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2423385/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2423385/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (5219167/8589934592)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (5219167/8589934592)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-11362443/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-11362443/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-5433419/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-5433419/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-2452037/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-2452037/134217728:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2423385/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2423385/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (5219167/8589934592)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (5219167/8589934592)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-11362443/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-11362443/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-5433419/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-5433419/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-2452037/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-2452037/134217728:ℚ) ≤ 0)]
theorem z0box_32 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 32 ≤ z0lay x 32 ∧ z0lay x 32 ≤ uzz0 32 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_32]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-5716417/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-5716417/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-2780951/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-2780951/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11962611/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11962611/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10579229/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10579229/268435456)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (1569829/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (1569829/16777216))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-5716417/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-5716417/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-2780951/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-2780951/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11962611/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11962611/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (10579229/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (10579229/268435456)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (1569829/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (1569829/16777216))]
theorem z0box_33 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 33 ≤ z0lay x 33 ∧ z0lay x 33 ≤ uzz0 33 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_33]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-6508637/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-6508637/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (11247727/134217728)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (11247727/134217728)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-9451237/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-9451237/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (6506371/1073741824)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (6506371/1073741824)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (1111865/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (1111865/134217728))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-6508637/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-6508637/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (11247727/134217728)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (11247727/134217728)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-9451237/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-9451237/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (6506371/1073741824)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (6506371/1073741824)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (1111865/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (1111865/134217728))]
theorem z0box_34 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 34 ≤ z0lay x 34 ∧ z0lay x 34 ≤ uzz0 34 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_34]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10876585/8388608)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10876585/8388608)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (3148325/33554432)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (3148325/33554432)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11775861/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11775861/67108864)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (8955007/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (8955007/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10025293/33554432)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10025293/33554432))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10876585/8388608)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10876585/8388608)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (3148325/33554432)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (3148325/33554432)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (11775861/67108864)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (11775861/67108864)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (8955007/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (8955007/67108864)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10025293/33554432)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10025293/33554432))]
theorem z0box_35 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 35 ≤ z0lay x 35 ∧ z0lay x 35 ≤ uzz0 35 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_35]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (2129767/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (2129767/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (5532673/16777216)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (5532673/16777216)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-8903769/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-8903769/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-6948519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-6948519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10280165/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10280165/134217728))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (2129767/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (2129767/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (5532673/16777216)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (5532673/16777216)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-8903769/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-8903769/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-6948519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-6948519/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (10280165/134217728)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (10280165/134217728))]
theorem z0box_36 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 36 ≤ z0lay x 36 ∧ z0lay x 36 ≤ uzz0 36 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_36]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2790769/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2790769/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-12387793/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-12387793/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-7775555/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-7775555/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-3467297/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-3467297/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (6762795/33554432)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (6762795/33554432))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2790769/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2790769/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-12387793/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-12387793/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-7775555/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-7775555/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-3467297/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-3467297/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (6762795/33554432)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (6762795/33554432))]
theorem z0box_37 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 37 ≤ z0lay x 37 ∧ z0lay x 37 ≤ uzz0 37 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_37]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-11099699/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-11099699/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (10957321/4294967296)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (10957321/4294967296)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2650035/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2650035/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (578569/8388608)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (578569/8388608)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14746133/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14746133/16777216:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-11099699/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-11099699/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (10957321/4294967296)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (10957321/4294967296)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (2650035/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (2650035/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (578569/8388608)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (578569/8388608)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-14746133/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-14746133/16777216:ℚ) ≤ 0)]
theorem z0box_38 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 38 ≤ z0lay x 38 ∧ z0lay x 38 ≤ uzz0 38 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_38]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-833749/524288:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-833749/524288:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12769743/268435456)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12769743/268435456)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (16386889/2147483648)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (16386889/2147483648)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-7655833/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-7655833/536870912:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (6121359/2147483648)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (6121359/2147483648))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-833749/524288:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-833749/524288:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12769743/268435456)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12769743/268435456)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (16386889/2147483648)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (16386889/2147483648)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-7655833/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-7655833/536870912:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (6121359/2147483648)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (6121359/2147483648))]
theorem z0box_39 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 39 ≤ z0lay x 39 ∧ z0lay x 39 ≤ uzz0 39 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_39]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (15214277/536870912)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (15214277/536870912)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-12392269/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-12392269/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-10244987/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-10244987/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-3236367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-3236367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (8372401/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (8372401/16777216))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (15214277/536870912)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (15214277/536870912)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-12392269/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-12392269/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-10244987/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-10244987/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-3236367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-3236367/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (8372401/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (8372401/16777216))]
theorem z0box_40 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 40 ≤ z0lay x 40 ∧ z0lay x 40 ≤ uzz0 40 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_40]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (9342359/67108864)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (9342359/67108864)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9599621/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9599621/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (14321199/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (14321199/33554432)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-692121/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-692121/2097152:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (1178029/4194304)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (1178029/4194304))]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (9342359/67108864)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (9342359/67108864)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9599621/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9599621/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (14321199/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (14321199/33554432)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-692121/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-692121/2097152:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (1178029/4194304)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (1178029/4194304))]
theorem z0box_41 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 41 ≤ z0lay x 41 ∧ z0lay x 41 ≤ uzz0 41 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_41]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (8652077/33554432)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (8652077/33554432)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-4206397/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-4206397/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5555473/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5555473/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (11069775/33554432)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (11069775/33554432)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-7183291/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-7183291/8388608:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (8652077/33554432)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (8652077/33554432)), mul_le_mul_of_nonpos_left h1u (by norm_num : (-4206397/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-4206397/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-5555473/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-5555473/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (11069775/33554432)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (11069775/33554432)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-7183291/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-7183291/8388608:ℚ) ≤ 0)]
theorem z0box_42 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 42 ≤ z0lay x 42 ∧ z0lay x 42 ≤ uzz0 42 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_42]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (9213779/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (9213779/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (10559735/4294967296)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (10559735/4294967296)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-1914079/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-1914079/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (1878357/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (1878357/67108864)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15527565/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15527565/8388608:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (9213779/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (9213779/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (10559735/4294967296)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (10559735/4294967296)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-1914079/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-1914079/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (1878357/67108864)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (1878357/67108864)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-15527565/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-15527565/8388608:ℚ) ≤ 0)]
theorem z0box_43 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 43 ≤ z0lay x 43 ∧ z0lay x 43 ≤ uzz0 43 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_43]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-12492147/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-12492147/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (6697207/2147483648)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (6697207/2147483648)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6304173/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6304173/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (7310947/536870912)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (7310947/536870912)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-8565775/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-8565775/536870912:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-12492147/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-12492147/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (6697207/2147483648)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (6697207/2147483648)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6304173/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6304173/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (7310947/536870912)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (7310947/536870912)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-8565775/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-8565775/536870912:ℚ) ≤ 0)]
theorem z0box_44 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 44 ≤ z0lay x 44 ∧ z0lay x 44 ≤ uzz0 44 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_44]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-1747217/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-1747217/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12956735/1073741824)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12956735/1073741824)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12928147/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12928147/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12234047/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12234047/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (4835093/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (4835093/16777216))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-1747217/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-1747217/4194304:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (12956735/1073741824)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (12956735/1073741824)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-12928147/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-12928147/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12234047/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12234047/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (4835093/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (4835093/16777216))]
theorem z0box_45 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 45 ≤ z0lay x 45 ∧ z0lay x 45 ≤ uzz0 45 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_45]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-10612243/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-10612243/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9627035/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9627035/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (7610387/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (7610387/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9900947/134217728)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9900947/134217728)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (545257/8388608)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (545257/8388608))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-10612243/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-10612243/16777216:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-9627035/268435456:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-9627035/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (7610387/268435456)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (7610387/268435456)), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (9900947/134217728)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (9900947/134217728)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (545257/8388608)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (545257/8388608))]
theorem z0box_46 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 46 ≤ z0lay x 46 ∧ z0lay x 46 ≤ uzz0 46 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_46]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (5261429/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (5261429/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (4735109/8388608)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (4735109/8388608)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (8818709/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (8818709/33554432)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-58555/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-58555/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-12008561/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-12008561/33554432:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (5261429/134217728)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (5261429/134217728)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (4735109/8388608)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (4735109/8388608)), mul_le_mul_of_nonneg_left h2u (by norm_num : (0:ℚ) ≤ (8818709/33554432)), mul_le_mul_of_nonneg_left h2l (by norm_num : (0:ℚ) ≤ (8818709/33554432)), mul_le_mul_of_nonpos_left h3u (by norm_num : (-58555/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-58555/4194304:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-12008561/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-12008561/33554432:ℚ) ≤ 0)]
theorem z0box_47 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 47 ≤ z0lay x 47 ∧ z0lay x 47 ≤ uzz0 47 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_47]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2589617/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2589617/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-259791/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-259791/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6397379/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6397379/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (11355813/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (11355813/268435456)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (837017/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (837017/16777216))]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-2589617/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-2589617/67108864:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1u (by norm_num : (-259791/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h1l (by norm_num : (-259791/2097152:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2u (by norm_num : (-6397379/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-6397379/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (11355813/268435456)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (11355813/268435456)), mul_le_mul_of_nonneg_left h4u (by norm_num : (0:ℚ) ≤ (837017/16777216)), mul_le_mul_of_nonneg_left h4l (by norm_num : (0:ℚ) ≤ (837017/16777216))]
theorem z0box_48 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 48 ≤ z0lay x 48 ∧ z0lay x 48 ≤ uzz0 48 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_48]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-13223047/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-13223047/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (15118835/34359738368)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (15118835/34359738368)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-4467711/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-4467711/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12436709/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12436709/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5301117/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5301117/1073741824:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonpos_left h0u (by norm_num : (-13223047/8388608:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h0l (by norm_num : (-13223047/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (15118835/34359738368)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (15118835/34359738368)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-4467711/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-4467711/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3u (by norm_num : (-12436709/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h3l (by norm_num : (-12436709/134217728:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4u (by norm_num : (-5301117/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-5301117/1073741824:ℚ) ≤ 0)]
theorem z0box_49 (x : Fin 5 → ℚ) (hb : inBox x) : lzz0 49 ≤ z0lay x 49 ∧ z0lay x 49 ≤ uzz0 49 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h1l,h1u⟩,⟨h2l,h2u⟩,⟨h3l,h3u⟩,⟨h4l,h4u⟩⟩ := hb
  rw [z0_49]; simp only [lzz0, uzz0, Matrix.cons_val]
  refine ⟨?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10408031/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10408031/16777216)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (10071349/134217728)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (10071349/134217728)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-7845885/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-7845885/536870912:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (8810555/33554432)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (8810555/33554432)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-8655299/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-8655299/33554432:ℚ) ≤ 0)]
  · linarith [mul_le_mul_of_nonneg_left h0u (by norm_num : (0:ℚ) ≤ (10408031/16777216)), mul_le_mul_of_nonneg_left h0l (by norm_num : (0:ℚ) ≤ (10408031/16777216)), mul_le_mul_of_nonneg_left h1u (by norm_num : (0:ℚ) ≤ (10071349/134217728)), mul_le_mul_of_nonneg_left h1l (by norm_num : (0:ℚ) ≤ (10071349/134217728)), mul_le_mul_of_nonpos_left h2u (by norm_num : (-7845885/536870912:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h2l (by norm_num : (-7845885/536870912:ℚ) ≤ 0), mul_le_mul_of_nonneg_left h3u (by norm_num : (0:ℚ) ≤ (8810555/33554432)), mul_le_mul_of_nonneg_left h3l (by norm_num : (0:ℚ) ≤ (8810555/33554432)), mul_le_mul_of_nonpos_left h4u (by norm_num : (-8655299/33554432:ℚ) ≤ 0), mul_le_mul_of_nonpos_left h4l (by norm_num : (-8655299/33554432:ℚ) ≤ 0)]
theorem aBox0 (x : Fin 5 → ℚ) (hb : inBox x) : ∀ k : Fin 50, 0 ≤ a0lay x k ∧ a0lay x k ≤ uz0 k := by
  intro k; fin_cases k
  · have hz := (z0box_0 x hb).2
    have hu : uzz0 0 ≤ uz0 0 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 0 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 0) ≤ uz0 0
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_1 x hb).2
    have hu : uzz0 1 ≤ uz0 1 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 1 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 1) ≤ uz0 1
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_2 x hb).2
    have hu : uzz0 2 ≤ uz0 2 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 2 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 2) ≤ uz0 2
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_3 x hb).2
    have hu : uzz0 3 ≤ uz0 3 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 3 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 3) ≤ uz0 3
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_4 x hb).2
    have hu : uzz0 4 ≤ uz0 4 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 4 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 4) ≤ uz0 4
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_5 x hb).2
    have hu : uzz0 5 ≤ uz0 5 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 5 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 5) ≤ uz0 5
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_6 x hb).2
    have hu : uzz0 6 ≤ uz0 6 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 6 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 6) ≤ uz0 6
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_7 x hb).2
    have hu : uzz0 7 ≤ uz0 7 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 7 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 7) ≤ uz0 7
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_8 x hb).2
    have hu : uzz0 8 ≤ uz0 8 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 8 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 8) ≤ uz0 8
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_9 x hb).2
    have hu : uzz0 9 ≤ uz0 9 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 9 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 9) ≤ uz0 9
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_10 x hb).2
    have hu : uzz0 10 ≤ uz0 10 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 10 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 10) ≤ uz0 10
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_11 x hb).2
    have hu : uzz0 11 ≤ uz0 11 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 11 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 11) ≤ uz0 11
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_12 x hb).2
    have hu : uzz0 12 ≤ uz0 12 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 12 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 12) ≤ uz0 12
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_13 x hb).2
    have hu : uzz0 13 ≤ uz0 13 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 13 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 13) ≤ uz0 13
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_14 x hb).2
    have hu : uzz0 14 ≤ uz0 14 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 14 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 14) ≤ uz0 14
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_15 x hb).2
    have hu : uzz0 15 ≤ uz0 15 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 15 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 15) ≤ uz0 15
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_16 x hb).2
    have hu : uzz0 16 ≤ uz0 16 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 16 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 16) ≤ uz0 16
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_17 x hb).2
    have hu : uzz0 17 ≤ uz0 17 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 17 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 17) ≤ uz0 17
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_18 x hb).2
    have hu : uzz0 18 ≤ uz0 18 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 18 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 18) ≤ uz0 18
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_19 x hb).2
    have hu : uzz0 19 ≤ uz0 19 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 19 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 19) ≤ uz0 19
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_20 x hb).2
    have hu : uzz0 20 ≤ uz0 20 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 20 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 20) ≤ uz0 20
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_21 x hb).2
    have hu : uzz0 21 ≤ uz0 21 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 21 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 21) ≤ uz0 21
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_22 x hb).2
    have hu : uzz0 22 ≤ uz0 22 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 22 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 22) ≤ uz0 22
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_23 x hb).2
    have hu : uzz0 23 ≤ uz0 23 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 23 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 23) ≤ uz0 23
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_24 x hb).2
    have hu : uzz0 24 ≤ uz0 24 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 24 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 24) ≤ uz0 24
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_25 x hb).2
    have hu : uzz0 25 ≤ uz0 25 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 25 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 25) ≤ uz0 25
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_26 x hb).2
    have hu : uzz0 26 ≤ uz0 26 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 26 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 26) ≤ uz0 26
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_27 x hb).2
    have hu : uzz0 27 ≤ uz0 27 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 27 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 27) ≤ uz0 27
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_28 x hb).2
    have hu : uzz0 28 ≤ uz0 28 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 28 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 28) ≤ uz0 28
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_29 x hb).2
    have hu : uzz0 29 ≤ uz0 29 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 29 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 29) ≤ uz0 29
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_30 x hb).2
    have hu : uzz0 30 ≤ uz0 30 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 30 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 30) ≤ uz0 30
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_31 x hb).2
    have hu : uzz0 31 ≤ uz0 31 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 31 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 31) ≤ uz0 31
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_32 x hb).2
    have hu : uzz0 32 ≤ uz0 32 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 32 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 32) ≤ uz0 32
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_33 x hb).2
    have hu : uzz0 33 ≤ uz0 33 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 33 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 33) ≤ uz0 33
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_34 x hb).2
    have hu : uzz0 34 ≤ uz0 34 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 34 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 34) ≤ uz0 34
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_35 x hb).2
    have hu : uzz0 35 ≤ uz0 35 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 35 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 35) ≤ uz0 35
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_36 x hb).2
    have hu : uzz0 36 ≤ uz0 36 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 36 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 36) ≤ uz0 36
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_37 x hb).2
    have hu : uzz0 37 ≤ uz0 37 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 37 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 37) ≤ uz0 37
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_38 x hb).2
    have hu : uzz0 38 ≤ uz0 38 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 38 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 38) ≤ uz0 38
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_39 x hb).2
    have hu : uzz0 39 ≤ uz0 39 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 39 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 39) ≤ uz0 39
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_40 x hb).2
    have hu : uzz0 40 ≤ uz0 40 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 40 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 40) ≤ uz0 40
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_41 x hb).2
    have hu : uzz0 41 ≤ uz0 41 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 41 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 41) ≤ uz0 41
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_42 x hb).2
    have hu : uzz0 42 ≤ uz0 42 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 42 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 42) ≤ uz0 42
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_43 x hb).2
    have hu : uzz0 43 ≤ uz0 43 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 43 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 43) ≤ uz0 43
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_44 x hb).2
    have hu : uzz0 44 ≤ uz0 44 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 44 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 44) ≤ uz0 44
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_45 x hb).2
    have hu : uzz0 45 ≤ uz0 45 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 45 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 45) ≤ uz0 45
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_46 x hb).2
    have hu : uzz0 46 ≤ uz0 46 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 46 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 46) ≤ uz0 46
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_47 x hb).2
    have hu : uzz0 47 ≤ uz0 47 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 47 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 47) ≤ uz0 47
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_48 x hb).2
    have hu : uzz0 48 ≤ uz0 48 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 48 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 48) ≤ uz0 48
    unfold relu; exact max_le h0 (le_trans hz hu)
  · have hz := (z0box_49 x hb).2
    have hu : uzz0 49 ≤ uz0 49 := by simp only [uz0, uzz0, Matrix.cons_val]; norm_num
    have h0 : (0:ℚ) ≤ uz0 49 := by simp only [uz0, Matrix.cons_val]; norm_num
    refine ⟨le_max_left _ _, ?_⟩
    show relu (z0lay x 49) ≤ uz0 49
    unfold relu; exact max_le h0 (le_trans hz hu)

/-- The CROWN/IBP upper bound on the real readout, over the post-ReLU box. -/
def cBound : ℚ := 553630694887348241/288230376151711744

theorem netEvalWide_eq (x : Fin 5 → ℚ) : netEvalWide x = (-12361587/67108864)*a0lay x 0 + (2307431/67108864)*a0lay x 1 + (-7727049/67108864)*a0lay x 2 + (3099641/16777216)*a0lay x 3 + (-4601923/33554432)*a0lay x 4 + (-12704849/67108864)*a0lay x 5 + (-6280509/8388608)*a0lay x 6 + (9661143/16777216)*a0lay x 7 + (-1787203/134217728)*a0lay x 8 + (301237/2097152)*a0lay x 9 + (8929975/67108864)*a0lay x 10 + (-15060437/67108864)*a0lay x 11 + (10138405/33554432)*a0lay x 12 + (10965293/268435456)*a0lay x 13 + (-11393709/33554432)*a0lay x 14 + (2178253/33554432)*a0lay x 15 + (2455151/33554432)*a0lay x 16 + (-15409235/33554432)*a0lay x 17 + (15929765/33554432)*a0lay x 18 + (3164401/8388608)*a0lay x 19 + (-9345497/8388608)*a0lay x 20 + (-9594101/16777216)*a0lay x 21 + (13398983/268435456)*a0lay x 22 + (-4264869/16777216)*a0lay x 23 + (-13552769/536870912)*a0lay x 24 + (7575517/33554432)*a0lay x 25 + (10063779/67108864)*a0lay x 26 + (-5207715/33554432)*a0lay x 27 + (-4617439/268435456)*a0lay x 28 + (16620953/16777216)*a0lay x 29 + (10520563/134217728)*a0lay x 30 + (-2419241/16777216)*a0lay x 31 + (-751095/4194304)*a0lay x 32 + (-2852437/8388608)*a0lay x 33 + (14248621/67108864)*a0lay x 34 + (554189/67108864)*a0lay x 35 + (2296103/33554432)*a0lay x 36 + (9864097/16777216)*a0lay x 37 + (-358009/2097152)*a0lay x 38 + (-9121605/16777216)*a0lay x 39 + (15962783/134217728)*a0lay x 40 + (-8319033/16777216)*a0lay x 41 + (-13979783/8388608)*a0lay x 42 + (-10874119/33554432)*a0lay x 43 + (-16560213/1073741824)*a0lay x 44 + (4279029/8388608)*a0lay x 45 + (12628519/134217728)*a0lay x 46 + (11320863/33554432)*a0lay x 47 + (3319129/8388608)*a0lay x 48 + (-14997019/67108864)*a0lay x 49 + (11213891/134217728) := by
  show (∑ j : Fin 50, Wr j * a0lay x j) + br = _
  simp [Fin.sum_univ_succ, Wr, br]; ring

theorem netEvalWide_upper_bound (x : Fin 5 → ℚ) (hb : inBox x) : netEvalWide x ≤ cBound := by
  have hb2 := aBox0 x hb
  have hpb : (0 ≤ a0lay x 0 ∧ a0lay x 0 ≤ (14760595147/8589934592)) ∧ (0 ≤ a0lay x 1 ∧ a0lay x 1 ≤ (0)) ∧ (0 ≤ a0lay x 2 ∧ a0lay x 2 ≤ (3023736455/8589934592)) ∧ (0 ≤ a0lay x 3 ∧ a0lay x 3 ≤ (0)) ∧ (0 ≤ a0lay x 4 ∧ a0lay x 4 ≤ (159834351/536870912)) ∧ (0 ≤ a0lay x 5 ∧ a0lay x 5 ≤ (7325652217/8589934592)) ∧ (0 ≤ a0lay x 6 ∧ a0lay x 6 ≤ (174136733/268435456)) ∧ (0 ≤ a0lay x 7 ∧ a0lay x 7 ≤ (0)) ∧ (0 ≤ a0lay x 8 ∧ a0lay x 8 ≤ (0)) ∧ (0 ≤ a0lay x 9 ∧ a0lay x 9 ≤ (0)) ∧ (0 ≤ a0lay x 10 ∧ a0lay x 10 ≤ (122747677/134217728)) ∧ (0 ≤ a0lay x 11 ∧ a0lay x 11 ≤ (612864466753/549755813888)) ∧ (0 ≤ a0lay x 12 ∧ a0lay x 12 ≤ (7560059821/17179869184)) ∧ (0 ≤ a0lay x 13 ∧ a0lay x 13 ≤ (0)) ∧ (0 ≤ a0lay x 14 ∧ a0lay x 14 ≤ (10084391141/17179869184)) ∧ (0 ≤ a0lay x 15 ∧ a0lay x 15 ≤ (11549037131/8589934592)) ∧ (0 ≤ a0lay x 16 ∧ a0lay x 16 ≤ (0)) ∧ (0 ≤ a0lay x 17 ∧ a0lay x 17 ≤ (6009801547/4294967296)) ∧ (0 ≤ a0lay x 18 ∧ a0lay x 18 ≤ (3186811173/8589934592)) ∧ (0 ≤ a0lay x 19 ∧ a0lay x 19 ≤ (0)) ∧ (0 ≤ a0lay x 20 ∧ a0lay x 20 ≤ (40474388605/34359738368)) ∧ (0 ≤ a0lay x 21 ∧ a0lay x 21 ≤ (0)) ∧ (0 ≤ a0lay x 22 ∧ a0lay x 22 ≤ (18792838575/8589934592)) ∧ (0 ≤ a0lay x 23 ∧ a0lay x 23 ≤ (4087723105/4294967296)) ∧ (0 ≤ a0lay x 24 ∧ a0lay x 24 ≤ (0)) ∧ (0 ≤ a0lay x 25 ∧ a0lay x 25 ≤ (0)) ∧ (0 ≤ a0lay x 26 ∧ a0lay x 26 ≤ (0)) ∧ (0 ≤ a0lay x 27 ∧ a0lay x 27 ≤ (784770183/1073741824)) ∧ (0 ≤ a0lay x 28 ∧ a0lay x 28 ≤ (626696549/536870912)) ∧ (0 ≤ a0lay x 29 ∧ a0lay x 29 ≤ (0)) ∧ (0 ≤ a0lay x 30 ∧ a0lay x 30 ≤ (26755925891/17179869184)) ∧ (0 ≤ a0lay x 31 ∧ a0lay x 31 ≤ (0)) ∧ (0 ≤ a0lay x 32 ∧ a0lay x 32 ≤ (0)) ∧ (0 ≤ a0lay x 33 ∧ a0lay x 33 ≤ (0)) ∧ (0 ≤ a0lay x 34 ∧ a0lay x 34 ≤ (7384617211/4294967296)) ∧ (0 ≤ a0lay x 35 ∧ a0lay x 35 ≤ (6203328525/17179869184)) ∧ (0 ≤ a0lay x 36 ∧ a0lay x 36 ≤ (3420631781/4294967296)) ∧ (0 ≤ a0lay x 37 ∧ a0lay x 37 ≤ (5548422823/8589934592)) ∧ (0 ≤ a0lay x 38 ∧ a0lay x 38 ≤ (0)) ∧ (0 ≤ a0lay x 39 ∧ a0lay x 39 ≤ (0)) ∧ (0 ≤ a0lay x 40 ∧ a0lay x 40 ≤ (584941743/1073741824)) ∧ (0 ≤ a0lay x 41 ∧ a0lay x 41 ≤ (2063260669/2147483648)) ∧ (0 ≤ a0lay x 42 ∧ a0lay x 42 ≤ (3094284891/8589934592)) ∧ (0 ≤ a0lay x 43 ∧ a0lay x 43 ≤ (0)) ∧ (0 ≤ a0lay x 44 ∧ a0lay x 44 ≤ (0)) ∧ (0 ≤ a0lay x 45 ∧ a0lay x 45 ≤ (0)) ∧ (0 ≤ a0lay x 46 ∧ a0lay x 46 ≤ (1396622539/2147483648)) ∧ (0 ≤ a0lay x 47 ∧ a0lay x 47 ≤ (126992671/268435456)) ∧ (0 ≤ a0lay x 48 ∧ a0lay x 48 ≤ (0)) ∧ (0 ≤ a0lay x 49 ∧ a0lay x 49 ≤ (974427749/1073741824)) := by
    refine ⟨⟨(hb2 0).1, by have := (hb2 0).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 1).1, by have := (hb2 1).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 2).1, by have := (hb2 2).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 3).1, by have := (hb2 3).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 4).1, by have := (hb2 4).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 5).1, by have := (hb2 5).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 6).1, by have := (hb2 6).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 7).1, by have := (hb2 7).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 8).1, by have := (hb2 8).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 9).1, by have := (hb2 9).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 10).1, by have := (hb2 10).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 11).1, by have := (hb2 11).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 12).1, by have := (hb2 12).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 13).1, by have := (hb2 13).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 14).1, by have := (hb2 14).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 15).1, by have := (hb2 15).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 16).1, by have := (hb2 16).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 17).1, by have := (hb2 17).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 18).1, by have := (hb2 18).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 19).1, by have := (hb2 19).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 20).1, by have := (hb2 20).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 21).1, by have := (hb2 21).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 22).1, by have := (hb2 22).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 23).1, by have := (hb2 23).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 24).1, by have := (hb2 24).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 25).1, by have := (hb2 25).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 26).1, by have := (hb2 26).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 27).1, by have := (hb2 27).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 28).1, by have := (hb2 28).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 29).1, by have := (hb2 29).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 30).1, by have := (hb2 30).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 31).1, by have := (hb2 31).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 32).1, by have := (hb2 32).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 33).1, by have := (hb2 33).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 34).1, by have := (hb2 34).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 35).1, by have := (hb2 35).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 36).1, by have := (hb2 36).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 37).1, by have := (hb2 37).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 38).1, by have := (hb2 38).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 39).1, by have := (hb2 39).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 40).1, by have := (hb2 40).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 41).1, by have := (hb2 41).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 42).1, by have := (hb2 42).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 43).1, by have := (hb2 43).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 44).1, by have := (hb2 44).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 45).1, by have := (hb2 45).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 46).1, by have := (hb2 46).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 47).1, by have := (hb2 47).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 48).1, by have := (hb2 48).2; simpa only [uz0, Matrix.cons_val] using this⟩, ⟨(hb2 49).1, by have := (hb2 49).2; simpa only [uz0, Matrix.cons_val] using this⟩⟩
  obtain ⟨⟨g0l, g0u⟩, ⟨g1l, g1u⟩, ⟨g2l, g2u⟩, ⟨g3l, g3u⟩, ⟨g4l, g4u⟩, ⟨g5l, g5u⟩, ⟨g6l, g6u⟩, ⟨g7l, g7u⟩, ⟨g8l, g8u⟩, ⟨g9l, g9u⟩, ⟨g10l, g10u⟩, ⟨g11l, g11u⟩, ⟨g12l, g12u⟩, ⟨g13l, g13u⟩, ⟨g14l, g14u⟩, ⟨g15l, g15u⟩, ⟨g16l, g16u⟩, ⟨g17l, g17u⟩, ⟨g18l, g18u⟩, ⟨g19l, g19u⟩, ⟨g20l, g20u⟩, ⟨g21l, g21u⟩, ⟨g22l, g22u⟩, ⟨g23l, g23u⟩, ⟨g24l, g24u⟩, ⟨g25l, g25u⟩, ⟨g26l, g26u⟩, ⟨g27l, g27u⟩, ⟨g28l, g28u⟩, ⟨g29l, g29u⟩, ⟨g30l, g30u⟩, ⟨g31l, g31u⟩, ⟨g32l, g32u⟩, ⟨g33l, g33u⟩, ⟨g34l, g34u⟩, ⟨g35l, g35u⟩, ⟨g36l, g36u⟩, ⟨g37l, g37u⟩, ⟨g38l, g38u⟩, ⟨g39l, g39u⟩, ⟨g40l, g40u⟩, ⟨g41l, g41u⟩, ⟨g42l, g42u⟩, ⟨g43l, g43u⟩, ⟨g44l, g44u⟩, ⟨g45l, g45u⟩, ⟨g46l, g46u⟩, ⟨g47l, g47u⟩, ⟨g48l, g48u⟩, ⟨g49l, g49u⟩⟩ := hpb
  rw [netEvalWide_eq]; simp only [cBound]
  linarith [mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-12361587/67108864:ℚ) ≤ 0) g0l, mul_le_mul_of_nonpos_left g0u (by norm_num : (-12361587/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g1u (by norm_num : (0:ℚ) ≤ (2307431/67108864)), mul_nonneg (by norm_num : (0:ℚ) ≤ (2307431/67108864)) g1l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-7727049/67108864:ℚ) ≤ 0) g2l, mul_le_mul_of_nonpos_left g2u (by norm_num : (-7727049/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g3u (by norm_num : (0:ℚ) ≤ (3099641/16777216)), mul_nonneg (by norm_num : (0:ℚ) ≤ (3099641/16777216)) g3l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-4601923/33554432:ℚ) ≤ 0) g4l, mul_le_mul_of_nonpos_left g4u (by norm_num : (-4601923/33554432:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-12704849/67108864:ℚ) ≤ 0) g5l, mul_le_mul_of_nonpos_left g5u (by norm_num : (-12704849/67108864:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-6280509/8388608:ℚ) ≤ 0) g6l, mul_le_mul_of_nonpos_left g6u (by norm_num : (-6280509/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g7u (by norm_num : (0:ℚ) ≤ (9661143/16777216)), mul_nonneg (by norm_num : (0:ℚ) ≤ (9661143/16777216)) g7l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-1787203/134217728:ℚ) ≤ 0) g8l, mul_le_mul_of_nonpos_left g8u (by norm_num : (-1787203/134217728:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g9u (by norm_num : (0:ℚ) ≤ (301237/2097152)), mul_nonneg (by norm_num : (0:ℚ) ≤ (301237/2097152)) g9l, mul_le_mul_of_nonneg_left g10u (by norm_num : (0:ℚ) ≤ (8929975/67108864)), mul_nonneg (by norm_num : (0:ℚ) ≤ (8929975/67108864)) g10l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-15060437/67108864:ℚ) ≤ 0) g11l, mul_le_mul_of_nonpos_left g11u (by norm_num : (-15060437/67108864:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g12u (by norm_num : (0:ℚ) ≤ (10138405/33554432)), mul_nonneg (by norm_num : (0:ℚ) ≤ (10138405/33554432)) g12l, mul_le_mul_of_nonneg_left g13u (by norm_num : (0:ℚ) ≤ (10965293/268435456)), mul_nonneg (by norm_num : (0:ℚ) ≤ (10965293/268435456)) g13l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-11393709/33554432:ℚ) ≤ 0) g14l, mul_le_mul_of_nonpos_left g14u (by norm_num : (-11393709/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g15u (by norm_num : (0:ℚ) ≤ (2178253/33554432)), mul_nonneg (by norm_num : (0:ℚ) ≤ (2178253/33554432)) g15l, mul_le_mul_of_nonneg_left g16u (by norm_num : (0:ℚ) ≤ (2455151/33554432)), mul_nonneg (by norm_num : (0:ℚ) ≤ (2455151/33554432)) g16l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-15409235/33554432:ℚ) ≤ 0) g17l, mul_le_mul_of_nonpos_left g17u (by norm_num : (-15409235/33554432:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g18u (by norm_num : (0:ℚ) ≤ (15929765/33554432)), mul_nonneg (by norm_num : (0:ℚ) ≤ (15929765/33554432)) g18l, mul_le_mul_of_nonneg_left g19u (by norm_num : (0:ℚ) ≤ (3164401/8388608)), mul_nonneg (by norm_num : (0:ℚ) ≤ (3164401/8388608)) g19l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-9345497/8388608:ℚ) ≤ 0) g20l, mul_le_mul_of_nonpos_left g20u (by norm_num : (-9345497/8388608:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-9594101/16777216:ℚ) ≤ 0) g21l, mul_le_mul_of_nonpos_left g21u (by norm_num : (-9594101/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g22u (by norm_num : (0:ℚ) ≤ (13398983/268435456)), mul_nonneg (by norm_num : (0:ℚ) ≤ (13398983/268435456)) g22l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-4264869/16777216:ℚ) ≤ 0) g23l, mul_le_mul_of_nonpos_left g23u (by norm_num : (-4264869/16777216:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-13552769/536870912:ℚ) ≤ 0) g24l, mul_le_mul_of_nonpos_left g24u (by norm_num : (-13552769/536870912:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g25u (by norm_num : (0:ℚ) ≤ (7575517/33554432)), mul_nonneg (by norm_num : (0:ℚ) ≤ (7575517/33554432)) g25l, mul_le_mul_of_nonneg_left g26u (by norm_num : (0:ℚ) ≤ (10063779/67108864)), mul_nonneg (by norm_num : (0:ℚ) ≤ (10063779/67108864)) g26l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-5207715/33554432:ℚ) ≤ 0) g27l, mul_le_mul_of_nonpos_left g27u (by norm_num : (-5207715/33554432:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-4617439/268435456:ℚ) ≤ 0) g28l, mul_le_mul_of_nonpos_left g28u (by norm_num : (-4617439/268435456:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g29u (by norm_num : (0:ℚ) ≤ (16620953/16777216)), mul_nonneg (by norm_num : (0:ℚ) ≤ (16620953/16777216)) g29l, mul_le_mul_of_nonneg_left g30u (by norm_num : (0:ℚ) ≤ (10520563/134217728)), mul_nonneg (by norm_num : (0:ℚ) ≤ (10520563/134217728)) g30l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2419241/16777216:ℚ) ≤ 0) g31l, mul_le_mul_of_nonpos_left g31u (by norm_num : (-2419241/16777216:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-751095/4194304:ℚ) ≤ 0) g32l, mul_le_mul_of_nonpos_left g32u (by norm_num : (-751095/4194304:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2852437/8388608:ℚ) ≤ 0) g33l, mul_le_mul_of_nonpos_left g33u (by norm_num : (-2852437/8388608:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g34u (by norm_num : (0:ℚ) ≤ (14248621/67108864)), mul_nonneg (by norm_num : (0:ℚ) ≤ (14248621/67108864)) g34l, mul_le_mul_of_nonneg_left g35u (by norm_num : (0:ℚ) ≤ (554189/67108864)), mul_nonneg (by norm_num : (0:ℚ) ≤ (554189/67108864)) g35l, mul_le_mul_of_nonneg_left g36u (by norm_num : (0:ℚ) ≤ (2296103/33554432)), mul_nonneg (by norm_num : (0:ℚ) ≤ (2296103/33554432)) g36l, mul_le_mul_of_nonneg_left g37u (by norm_num : (0:ℚ) ≤ (9864097/16777216)), mul_nonneg (by norm_num : (0:ℚ) ≤ (9864097/16777216)) g37l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-358009/2097152:ℚ) ≤ 0) g38l, mul_le_mul_of_nonpos_left g38u (by norm_num : (-358009/2097152:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-9121605/16777216:ℚ) ≤ 0) g39l, mul_le_mul_of_nonpos_left g39u (by norm_num : (-9121605/16777216:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g40u (by norm_num : (0:ℚ) ≤ (15962783/134217728)), mul_nonneg (by norm_num : (0:ℚ) ≤ (15962783/134217728)) g40l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-8319033/16777216:ℚ) ≤ 0) g41l, mul_le_mul_of_nonpos_left g41u (by norm_num : (-8319033/16777216:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-13979783/8388608:ℚ) ≤ 0) g42l, mul_le_mul_of_nonpos_left g42u (by norm_num : (-13979783/8388608:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-10874119/33554432:ℚ) ≤ 0) g43l, mul_le_mul_of_nonpos_left g43u (by norm_num : (-10874119/33554432:ℚ) ≤ 0), mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-16560213/1073741824:ℚ) ≤ 0) g44l, mul_le_mul_of_nonpos_left g44u (by norm_num : (-16560213/1073741824:ℚ) ≤ 0), mul_le_mul_of_nonneg_left g45u (by norm_num : (0:ℚ) ≤ (4279029/8388608)), mul_nonneg (by norm_num : (0:ℚ) ≤ (4279029/8388608)) g45l, mul_le_mul_of_nonneg_left g46u (by norm_num : (0:ℚ) ≤ (12628519/134217728)), mul_nonneg (by norm_num : (0:ℚ) ≤ (12628519/134217728)) g46l, mul_le_mul_of_nonneg_left g47u (by norm_num : (0:ℚ) ≤ (11320863/33554432)), mul_nonneg (by norm_num : (0:ℚ) ≤ (11320863/33554432)) g47l, mul_le_mul_of_nonneg_left g48u (by norm_num : (0:ℚ) ≤ (3319129/8388608)), mul_nonneg (by norm_num : (0:ℚ) ≤ (3319129/8388608)) g48l, mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-14997019/67108864:ℚ) ≤ 0) g49l, mul_le_mul_of_nonpos_left g49u (by norm_num : (-14997019/67108864:ℚ) ≤ 0)]

/-! ## Bridge-based Farkas certificate (Bridge.farkas_premise_combination). -/
structure WState where
  a : Fin 50 → ℚ
  y : ℚ
def genuine (x : Fin 5 → ℚ) : WState where
  a := fun j => a0lay x j
  y := -netEvalWide x
def valid (st : WState) : Prop := ∃ x : Fin 5 → ℚ, inBox x ∧ st = genuine x
def prem (i : Fin 100) (st : WState) : ℚ :=
  if h : (i : ℕ) < 50 then -(st.a ⟨(i:ℕ), h⟩)
  else st.a ⟨(i:ℕ) - 50, by omega⟩ - uz0 ⟨(i:ℕ) - 50, by omega⟩
theorem bridge_premises_sound (i : Fin 100) (st : WState) (hv : valid st) : prem i st ≤ 0 := by
  obtain ⟨x, hb, rfl⟩ := hv
  have hb2 := aBox0 x hb
  unfold prem
  by_cases h : (i : ℕ) < 50
  · simp only [h, dif_pos, genuine]
    have := (hb2 ⟨(i:ℕ), h⟩).1; linarith
  · simp only [h, dif_neg, not_false_iff, genuine]
    have hk := (hb2 ⟨(i:ℕ)-50, by omega⟩).2
    linarith [hk]

def thr : ℚ := 3991125645861615/1000000000000000
theorem cBound_val : cBound = 553630694887348241/288230376151711744 := rfl
/-- cBound ≈ 1.920792; prop_1 threshold = 3.991125645861615. -/
theorem cBound_lt_thr : cBound < thr := by norm_num [cBound, thr]
/-- DECISION: the real wide readout is below the prop_1 threshold on the whole box. -/
theorem netEvalWide_below_thr (x : Fin 5 → ℚ) (hb : inBox x) : netEvalWide x < thr := by
  have := netEvalWide_upper_bound x hb; have := cBound_lt_thr; linarith

#print axioms netEvalWide
#print axioms netEvalWide_eq
#print axioms bridge_premises_sound
#print axioms netEvalWide_upper_bound
#print axioms netEvalWide_below_thr
#print axioms aBox0

end NetAcasWide
end Crownproof