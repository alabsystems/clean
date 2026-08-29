/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

REAL ViT block 1.0 — FINAL end-to-end composition (block-output bound).

Threads the per-stage box theorems (proven coordinate-by-coordinate in
`VFBbn1/VFBvalue/VFBao/VFBbn2/VFBhid/VFBmlp` on the REAL pretrained weights of
`vit_2023/pgd_2_3_16.onnx`) through the genuine block dataflow and emits the
kernel-checked block-output bound  `z_o ∈ [zLo_o, zHi_o]`  for the block-output
coord(s) DSL.  See `VitFullBlock.lean` for the full architecture/honesty notes.

The genuine nonlinear bridges enter HERE:
  * BatchNorm1/2 : `bn_channel_box` per channel (REAL `Real.sqrt` normalizer);
  * Attention    : `softmax_readout_mem` (REAL softmax simplex / barycentric readout);
  * ReLU         : `reluR_box` (monotone interval map);
the dense layers via `dot_ibpR` (sound IBP over the REAL weights), and the two
residual adds exactly.

`#print axioms` MUST be [propext, Classical.choice, Quot.sound] — NO sorryAx.
-/

import Crownproof.VFBbn1
import Crownproof.VFBvalue
import Crownproof.VFBao
import Crownproof.VFBbn2
import Crownproof.VFBhid
import Crownproof.VFBmlp

namespace Crownproof.VitFullBlock

open Crownproof Crownproof.SoftmaxBridge Finset Real

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

/-! ## 5. REAL weight matrices / biases as `o`-indexed selectors. -/

def bvv : Fin 48 → ℚ := ![(637035/4194304), (8623141/268435456), (-11402589/268435456), (5929069/268435456), (-11034523/1073741824), (-8912905/2147483648), (14131957/4294967296), (15055495/536870912), (-8868687/67108864), (12750141/134217728), (9052091/67108864), (-12969957/134217728), (-8986967/536870912), (14730433/134217728), (-15885221/268435456), (-11412131/134217728), (5205779/67108864), (-10952625/268435456), (8297445/134217728), (-7803393/134217728), (14953293/134217728), (902631/8388608), (3554927/33554432), (-12956763/268435456), (5541929/33554432), (-13757819/1073741824), (13631803/134217728), (-12564167/268435456), (2160099/33554432), (-13856073/134217728), (2754177/67108864), (4402007/67108864), (12400953/67108864), (-9308059/67108864), (7914533/268435456), (-8496707/67108864), (-8491777/67108864), (3444655/33554432), (9337207/134217728), (16032367/134217728), (5497051/67108864), (-533143/8388608), (11063695/4294967296), (15721161/134217728), (-4202759/268435456), (2169457/16777216), (-332127/16777216), (11280707/134217728)]
def bovv : Fin 48 → ℚ := ![(11858621/536870912), (-14957377/134217728), (-4073987/134217728), (-15608359/268435456), (6169579/33554432), (4789201/33554432), (3401709/134217728), (14773671/134217728), (3893795/268435456), (-8781393/268435456), (-3849221/33554432), (14567651/134217728), (3590867/67108864), (-11105143/536870912), (-778145/8388608), (15276627/134217728), (2426937/33554432), (-4931749/67108864), (9165293/67108864), (-833717/8388608), (-13648761/536870912), (339505/33554432), (8418327/67108864), (14200207/1073741824), (7237779/67108864), (-188539/2097152), (10850525/134217728), (16254697/134217728), (-11413475/134217728), (-11416341/268435456), (1381529/33554432), (3774273/134217728), (4320239/134217728), (-8700849/268435456), (-5480185/134217728), (15054631/134217728), (-4341217/67108864), (15440753/268435456), (-12526709/134217728), (-15281647/134217728), (-3543553/33554432), (16264875/134217728), (-1592109/33554432), (-6226875/67108864), (5216749/268435456), (16662505/134217728), (13866335/17179869184), (10913905/536870912)]
def b1vv : Fin 96 → ℚ := ![(-6872831/16777216), (-13352245/16777216), (-3647675/134217728), (-6609297/8388608), (-2793161/33554432), (-13642847/16777216), (-772723/16777216), (-4934107/33554432), (-1153469/2097152), (-638711/524288), (9769761/134217728), (-10507531/33554432), (-8328237/16777216), (-5640541/4194304), (11143047/33554432), (4387685/2097152), (5544177/33554432), (-5494207/4194304), (-4550279/33554432), (-3639715/8388608), (-2317659/33554432), (-2115475/2097152), (16162583/67108864), (-3900519/4194304), (-10985335/134217728), (-4476169/8388608), (-12967475/16777216), (-650751/16777216), (-10234557/4194304), (-1562439/2097152), (5393139/16777216), (-8874343/134217728), (-8736221/67108864), (-9413953/8388608), (-13880627/33554432), (-16776817/8388608), (16424459/134217728), (-5150943/134217728), (-9730433/33554432), (-5906987/67108864), (-7549317/67108864), (-6242439/8388608), (3837163/16777216), (-11310435/8388608), (9259801/16777216), (-11757417/67108864), (-4866297/16777216), (14181223/134217728), (-2294063/4194304), (-4861977/33554432), (-11588965/33554432), (-16670097/33554432), (-12829105/8388608), (-5456869/8388608), (-5907993/8388608), (-8692335/67108864), (-11633705/16777216), (-1044569/2097152), (8931459/8388608), (-12629791/67108864), (-11376827/134217728), (-9272273/16777216), (15400253/16777216), (7409085/16777216), (-7296363/8388608), (-5581791/8388608), (-1770415/1048576), (-8506611/4194304), (-2626991/4194304), (-10510835/67108864), (-10789881/16777216), (-915911/8388608), (5320289/8388608), (-7623919/8388608), (-9012697/16777216), (-4701711/4194304), (-1001341/16777216), (9585243/8388608), (-14200009/268435456), (-11458291/134217728), (-1328445/2097152), (-13496547/8388608), (-3891469/4194304), (-10499055/8388608), (-13779039/33554432), (-5588977/16777216), (8973265/33554432), (-8829139/16777216), (-14830557/8388608), (-13866301/16777216), (-10741747/4294967296), (-11785159/8388608), (-14983347/134217728), (-5090165/16777216), (-9184041/16777216), (-3033805/16777216)]
def b2vv : Fin 48 → ℚ := ![(9728007/1073741824), (48109/4194304), (-9977679/4294967296), (4422461/1073741824), (9657345/1073741824), (13816921/134217728), (1687057/67108864), (2470691/67108864), (-8524203/268435456), (12195777/134217728), (11247283/8589934592), (-5881819/34359738368), (16499361/268435456), (-9696951/134217728), (12714455/134217728), (-12601597/268435456), (12242231/134217728), (5293727/134217728), (-12811879/268435456), (-6548509/536870912), (-364385/16777216), (11796317/268435456), (11251577/134217728), (-1081267/16777216), (13657027/134217728), (7139819/67108864), (6504671/67108864), (1552653/16777216), (4893975/134217728), (-6957389/67108864), (-9355029/134217728), (-15279793/268435456), (5668605/536870912), (13405269/268435456), (8419983/536870912), (6453571/67108864), (-14206255/68719476736), (81527/1048576), (1952105/33554432), (-10445423/134217728), (10373033/268435456), (12692907/268435456), (10532055/134217728), (-6609747/67108864), (-7485571/134217728), (-11137835/134217728), (-5274129/268435456), (-13876229/268435456)]

def WvRow : Fin 48 → Fin 48 → ℚ := ![Wv0, Wv1, Wv2, Wv3, Wv4, Wv5, Wv6, Wv7, Wv8, Wv9, Wv10, Wv11, Wv12, Wv13, Wv14, Wv15, Wv16, Wv17, Wv18, Wv19, Wv20, Wv21, Wv22, Wv23, Wv24, Wv25, Wv26, Wv27, Wv28, Wv29, Wv30, Wv31, Wv32, Wv33, Wv34, Wv35, Wv36, Wv37, Wv38, Wv39, Wv40, Wv41, Wv42, Wv43, Wv44, Wv45, Wv46, Wv47]
def WoRow : Fin 48 → Fin 48 → ℚ := ![Wo0, Wo1, Wo2, Wo3, Wo4, Wo5, Wo6, Wo7, Wo8, Wo9, Wo10, Wo11, Wo12, Wo13, Wo14, Wo15, Wo16, Wo17, Wo18, Wo19, Wo20, Wo21, Wo22, Wo23, Wo24, Wo25, Wo26, Wo27, Wo28, Wo29, Wo30, Wo31, Wo32, Wo33, Wo34, Wo35, Wo36, Wo37, Wo38, Wo39, Wo40, Wo41, Wo42, Wo43, Wo44, Wo45, Wo46, Wo47]

def W1Row : Fin 96 → Fin 48 → ℚ := ![W1_0, W1_1, W1_2, W1_3, W1_4, W1_5, W1_6, W1_7, W1_8, W1_9, W1_10, W1_11, W1_12, W1_13, W1_14, W1_15, W1_16, W1_17, W1_18, W1_19, W1_20, W1_21, W1_22, W1_23, W1_24, W1_25, W1_26, W1_27, W1_28, W1_29, W1_30, W1_31, W1_32, W1_33, W1_34, W1_35, W1_36, W1_37, W1_38, W1_39, W1_40, W1_41, W1_42, W1_43, W1_44, W1_45, W1_46, W1_47, W1_48, W1_49, W1_50, W1_51, W1_52, W1_53, W1_54, W1_55, W1_56, W1_57, W1_58, W1_59, W1_60, W1_61, W1_62, W1_63, W1_64, W1_65, W1_66, W1_67, W1_68, W1_69, W1_70, W1_71, W1_72, W1_73, W1_74, W1_75, W1_76, W1_77, W1_78, W1_79, W1_80, W1_81, W1_82, W1_83, W1_84, W1_85, W1_86, W1_87, W1_88, W1_89, W1_90, W1_91, W1_92, W1_93, W1_94, W1_95]

def W2Row : Fin 48 → Fin 96 → ℚ := ![W2_0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## 6. Genuine block functions over an abstract input `x` in the box. -/

/-- BatchNorm1 output, channel `o` (REAL affine, `Real.sqrt` normalizer). -/
noncomputable def n1f (x : Fin 48 → ℝ) (o : Fin 48) : ℝ :=
  ((bn1_bias o:ℚ):ℝ) + ((bn1_weight o:ℚ):ℝ) * (rsqrt ((2748779/274877906944:ℚ):ℝ) ((bn1_var o:ℚ):ℝ) * (x o - ((bn1_mean o:ℚ):ℝ)))

/-- BatchNorm2 output, channel `o`. -/
noncomputable def n2f (y : Fin 48 → ℝ) (o : Fin 48) : ℝ :=
  ((bn2_bias o:ℚ):ℝ) + ((bn2_weight o:ℚ):ℝ) * (rsqrt ((2748779/274877906944:ℚ):ℝ) ((bn2_var o:ℚ):ℝ) * (y o - ((bn2_mean o:ℚ):ℝ)))

/-- Attention OUT-projection (MatMul_223), coord `o`:  `b_o + Σ_p W_o[o][p]·att_p`. -/
noncomputable def aof (att : Fin 48 → ℝ) (o : Fin 48) : ℝ :=
  ((bovv o:ℚ):ℝ) + ∑ p, ((WoRow o p:ℚ):ℝ) * att p

/-- MLP hidden pre-activation (MatMul_224), coord `o`:  `b1_o + Σ_p W1[o][p]·n2_p`. -/
noncomputable def hf (n2 : Fin 48 → ℝ) (o : Fin 96) : ℝ :=
  ((b1vv o:ℚ):ℝ) + ∑ p, ((W1Row o p:ℚ):ℝ) * n2 p

/-- MLP output (MatMul_225), coord `o`:  `b2_o + Σ_p W2[o][p]·rl_p`. -/
noncomputable def mf (rl : Fin 96 → ℝ) (o : Fin 48) : ℝ :=
  ((b2vv o:ℚ):ℝ) + ∑ p, ((W2Row o p:ℚ):ℝ) * rl p

/-- Value-range projection (MatMul of `W_v`), coord `o`:  `b_v,o + Σ_p W_v[o][p]·n1_p`. -/
noncomputable def vf (n1 : Fin 48 → ℝ) (o : Fin 48) : ℝ :=
  ((bvv o:ℚ):ℝ) + ∑ p, ((WvRow o p:ℚ):ℝ) * n1 p

/-! ## 7. Per-stage box theorems (bundled from the per-coordinate lemmas). -/

/-- **BatchNorm1 box** (all 48 channels), from the input box. -/
theorem n1_box (x : Fin 48 → ℝ) (hl : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hh : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ∀ o, ((n1Lo o:ℚ):ℝ) ≤ n1f x o ∧ n1f x o ≤ ((n1Hi o:ℚ):ℝ) := by
  intro o; unfold n1f; fin_cases o
  · exact bn1_c0 x hl hh
  · exact bn1_c1 x hl hh
  · exact bn1_c2 x hl hh
  · exact bn1_c3 x hl hh
  · exact bn1_c4 x hl hh
  · exact bn1_c5 x hl hh
  · exact bn1_c6 x hl hh
  · exact bn1_c7 x hl hh
  · exact bn1_c8 x hl hh
  · exact bn1_c9 x hl hh
  · exact bn1_c10 x hl hh
  · exact bn1_c11 x hl hh
  · exact bn1_c12 x hl hh
  · exact bn1_c13 x hl hh
  · exact bn1_c14 x hl hh
  · exact bn1_c15 x hl hh
  · exact bn1_c16 x hl hh
  · exact bn1_c17 x hl hh
  · exact bn1_c18 x hl hh
  · exact bn1_c19 x hl hh
  · exact bn1_c20 x hl hh
  · exact bn1_c21 x hl hh
  · exact bn1_c22 x hl hh
  · exact bn1_c23 x hl hh
  · exact bn1_c24 x hl hh
  · exact bn1_c25 x hl hh
  · exact bn1_c26 x hl hh
  · exact bn1_c27 x hl hh
  · exact bn1_c28 x hl hh
  · exact bn1_c29 x hl hh
  · exact bn1_c30 x hl hh
  · exact bn1_c31 x hl hh
  · exact bn1_c32 x hl hh
  · exact bn1_c33 x hl hh
  · exact bn1_c34 x hl hh
  · exact bn1_c35 x hl hh
  · exact bn1_c36 x hl hh
  · exact bn1_c37 x hl hh
  · exact bn1_c38 x hl hh
  · exact bn1_c39 x hl hh
  · exact bn1_c40 x hl hh
  · exact bn1_c41 x hl hh
  · exact bn1_c42 x hl hh
  · exact bn1_c43 x hl hh
  · exact bn1_c44 x hl hh
  · exact bn1_c45 x hl hh
  · exact bn1_c46 x hl hh
  · exact bn1_c47 x hl hh

/-- **Value range box** (all 48 coords): the genuine `W_v n1 + b_v` projection of
    the n1 box.  This is the value interval the softmax readout stays within. -/
theorem value_box (n1 : Fin 48 → ℝ) (hl : ∀ jj, ((n1Lo jj:ℚ):ℝ) ≤ n1 jj) (hh : ∀ jj, n1 jj ≤ ((n1Hi jj:ℚ):ℝ)) :
    ∀ o, ((vLo o:ℚ):ℝ) ≤ vf n1 o ∧ vf n1 o ≤ ((vHi o:ℚ):ℝ) := by
  intro o; unfold vf; fin_cases o <;> simp only [bvv, WvRow, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact value_c0 n1 hl hh
  · exact value_c1 n1 hl hh
  · exact value_c2 n1 hl hh
  · exact value_c3 n1 hl hh
  · exact value_c4 n1 hl hh
  · exact value_c5 n1 hl hh
  · exact value_c6 n1 hl hh
  · exact value_c7 n1 hl hh
  · exact value_c8 n1 hl hh
  · exact value_c9 n1 hl hh
  · exact value_c10 n1 hl hh
  · exact value_c11 n1 hl hh
  · exact value_c12 n1 hl hh
  · exact value_c13 n1 hl hh
  · exact value_c14 n1 hl hh
  · exact value_c15 n1 hl hh
  · exact value_c16 n1 hl hh
  · exact value_c17 n1 hl hh
  · exact value_c18 n1 hl hh
  · exact value_c19 n1 hl hh
  · exact value_c20 n1 hl hh
  · exact value_c21 n1 hl hh
  · exact value_c22 n1 hl hh
  · exact value_c23 n1 hl hh
  · exact value_c24 n1 hl hh
  · exact value_c25 n1 hl hh
  · exact value_c26 n1 hl hh
  · exact value_c27 n1 hl hh
  · exact value_c28 n1 hl hh
  · exact value_c29 n1 hl hh
  · exact value_c30 n1 hl hh
  · exact value_c31 n1 hl hh
  · exact value_c32 n1 hl hh
  · exact value_c33 n1 hl hh
  · exact value_c34 n1 hl hh
  · exact value_c35 n1 hl hh
  · exact value_c36 n1 hl hh
  · exact value_c37 n1 hl hh
  · exact value_c38 n1 hl hh
  · exact value_c39 n1 hl hh
  · exact value_c40 n1 hl hh
  · exact value_c41 n1 hl hh
  · exact value_c42 n1 hl hh
  · exact value_c43 n1 hl hh
  · exact value_c44 n1 hl hh
  · exact value_c45 n1 hl hh
  · exact value_c46 n1 hl hh
  · exact value_c47 n1 hl hh

/-- **Attention out-projection box** (all 48 coords) from the attention box. -/
theorem ao_box (att : Fin 48 → ℝ) (hl : ∀ jj, ((vLo jj:ℚ):ℝ) ≤ att jj) (hh : ∀ jj, att jj ≤ ((vHi jj:ℚ):ℝ)) :
    ∀ o, ((aoLo o:ℚ):ℝ) ≤ aof att o ∧ aof att o ≤ ((aoHi o:ℚ):ℝ) := by
  intro o; unfold aof; fin_cases o <;> simp only [bovv, WoRow, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact ao_c0 att hl hh
  · exact ao_c1 att hl hh
  · exact ao_c2 att hl hh
  · exact ao_c3 att hl hh
  · exact ao_c4 att hl hh
  · exact ao_c5 att hl hh
  · exact ao_c6 att hl hh
  · exact ao_c7 att hl hh
  · exact ao_c8 att hl hh
  · exact ao_c9 att hl hh
  · exact ao_c10 att hl hh
  · exact ao_c11 att hl hh
  · exact ao_c12 att hl hh
  · exact ao_c13 att hl hh
  · exact ao_c14 att hl hh
  · exact ao_c15 att hl hh
  · exact ao_c16 att hl hh
  · exact ao_c17 att hl hh
  · exact ao_c18 att hl hh
  · exact ao_c19 att hl hh
  · exact ao_c20 att hl hh
  · exact ao_c21 att hl hh
  · exact ao_c22 att hl hh
  · exact ao_c23 att hl hh
  · exact ao_c24 att hl hh
  · exact ao_c25 att hl hh
  · exact ao_c26 att hl hh
  · exact ao_c27 att hl hh
  · exact ao_c28 att hl hh
  · exact ao_c29 att hl hh
  · exact ao_c30 att hl hh
  · exact ao_c31 att hl hh
  · exact ao_c32 att hl hh
  · exact ao_c33 att hl hh
  · exact ao_c34 att hl hh
  · exact ao_c35 att hl hh
  · exact ao_c36 att hl hh
  · exact ao_c37 att hl hh
  · exact ao_c38 att hl hh
  · exact ao_c39 att hl hh
  · exact ao_c40 att hl hh
  · exact ao_c41 att hl hh
  · exact ao_c42 att hl hh
  · exact ao_c43 att hl hh
  · exact ao_c44 att hl hh
  · exact ao_c45 att hl hh
  · exact ao_c46 att hl hh
  · exact ao_c47 att hl hh

/-- **BatchNorm2 box** (all 48 channels) from the residual-1 box. -/
theorem n2_box (y : Fin 48 → ℝ) (hl : ∀ jj, ((yLo jj:ℚ):ℝ) ≤ y jj) (hh : ∀ jj, y jj ≤ ((yHi jj:ℚ):ℝ)) :
    ∀ o, ((n2Lo o:ℚ):ℝ) ≤ n2f y o ∧ n2f y o ≤ ((n2Hi o:ℚ):ℝ) := by
  intro o; unfold n2f; fin_cases o
  · exact bn2_c0 y hl hh
  · exact bn2_c1 y hl hh
  · exact bn2_c2 y hl hh
  · exact bn2_c3 y hl hh
  · exact bn2_c4 y hl hh
  · exact bn2_c5 y hl hh
  · exact bn2_c6 y hl hh
  · exact bn2_c7 y hl hh
  · exact bn2_c8 y hl hh
  · exact bn2_c9 y hl hh
  · exact bn2_c10 y hl hh
  · exact bn2_c11 y hl hh
  · exact bn2_c12 y hl hh
  · exact bn2_c13 y hl hh
  · exact bn2_c14 y hl hh
  · exact bn2_c15 y hl hh
  · exact bn2_c16 y hl hh
  · exact bn2_c17 y hl hh
  · exact bn2_c18 y hl hh
  · exact bn2_c19 y hl hh
  · exact bn2_c20 y hl hh
  · exact bn2_c21 y hl hh
  · exact bn2_c22 y hl hh
  · exact bn2_c23 y hl hh
  · exact bn2_c24 y hl hh
  · exact bn2_c25 y hl hh
  · exact bn2_c26 y hl hh
  · exact bn2_c27 y hl hh
  · exact bn2_c28 y hl hh
  · exact bn2_c29 y hl hh
  · exact bn2_c30 y hl hh
  · exact bn2_c31 y hl hh
  · exact bn2_c32 y hl hh
  · exact bn2_c33 y hl hh
  · exact bn2_c34 y hl hh
  · exact bn2_c35 y hl hh
  · exact bn2_c36 y hl hh
  · exact bn2_c37 y hl hh
  · exact bn2_c38 y hl hh
  · exact bn2_c39 y hl hh
  · exact bn2_c40 y hl hh
  · exact bn2_c41 y hl hh
  · exact bn2_c42 y hl hh
  · exact bn2_c43 y hl hh
  · exact bn2_c44 y hl hh
  · exact bn2_c45 y hl hh
  · exact bn2_c46 y hl hh
  · exact bn2_c47 y hl hh

/-- **MLP hidden box** (all 96 coords) from the BN2 box. -/
theorem h_box (n2 : Fin 48 → ℝ) (hl : ∀ jj, ((n2Lo jj:ℚ):ℝ) ≤ n2 jj) (hh : ∀ jj, n2 jj ≤ ((n2Hi jj:ℚ):ℝ)) :
    ∀ o, ((hLo o:ℚ):ℝ) ≤ hf n2 o ∧ hf n2 o ≤ ((hHi o:ℚ):ℝ) := by
  intro o; unfold hf; fin_cases o <;> simp only [b1vv, W1Row, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact hid_c0 n2 hl hh
  · exact hid_c1 n2 hl hh
  · exact hid_c2 n2 hl hh
  · exact hid_c3 n2 hl hh
  · exact hid_c4 n2 hl hh
  · exact hid_c5 n2 hl hh
  · exact hid_c6 n2 hl hh
  · exact hid_c7 n2 hl hh
  · exact hid_c8 n2 hl hh
  · exact hid_c9 n2 hl hh
  · exact hid_c10 n2 hl hh
  · exact hid_c11 n2 hl hh
  · exact hid_c12 n2 hl hh
  · exact hid_c13 n2 hl hh
  · exact hid_c14 n2 hl hh
  · exact hid_c15 n2 hl hh
  · exact hid_c16 n2 hl hh
  · exact hid_c17 n2 hl hh
  · exact hid_c18 n2 hl hh
  · exact hid_c19 n2 hl hh
  · exact hid_c20 n2 hl hh
  · exact hid_c21 n2 hl hh
  · exact hid_c22 n2 hl hh
  · exact hid_c23 n2 hl hh
  · exact hid_c24 n2 hl hh
  · exact hid_c25 n2 hl hh
  · exact hid_c26 n2 hl hh
  · exact hid_c27 n2 hl hh
  · exact hid_c28 n2 hl hh
  · exact hid_c29 n2 hl hh
  · exact hid_c30 n2 hl hh
  · exact hid_c31 n2 hl hh
  · exact hid_c32 n2 hl hh
  · exact hid_c33 n2 hl hh
  · exact hid_c34 n2 hl hh
  · exact hid_c35 n2 hl hh
  · exact hid_c36 n2 hl hh
  · exact hid_c37 n2 hl hh
  · exact hid_c38 n2 hl hh
  · exact hid_c39 n2 hl hh
  · exact hid_c40 n2 hl hh
  · exact hid_c41 n2 hl hh
  · exact hid_c42 n2 hl hh
  · exact hid_c43 n2 hl hh
  · exact hid_c44 n2 hl hh
  · exact hid_c45 n2 hl hh
  · exact hid_c46 n2 hl hh
  · exact hid_c47 n2 hl hh
  · exact hid_c48 n2 hl hh
  · exact hid_c49 n2 hl hh
  · exact hid_c50 n2 hl hh
  · exact hid_c51 n2 hl hh
  · exact hid_c52 n2 hl hh
  · exact hid_c53 n2 hl hh
  · exact hid_c54 n2 hl hh
  · exact hid_c55 n2 hl hh
  · exact hid_c56 n2 hl hh
  · exact hid_c57 n2 hl hh
  · exact hid_c58 n2 hl hh
  · exact hid_c59 n2 hl hh
  · exact hid_c60 n2 hl hh
  · exact hid_c61 n2 hl hh
  · exact hid_c62 n2 hl hh
  · exact hid_c63 n2 hl hh
  · exact hid_c64 n2 hl hh
  · exact hid_c65 n2 hl hh
  · exact hid_c66 n2 hl hh
  · exact hid_c67 n2 hl hh
  · exact hid_c68 n2 hl hh
  · exact hid_c69 n2 hl hh
  · exact hid_c70 n2 hl hh
  · exact hid_c71 n2 hl hh
  · exact hid_c72 n2 hl hh
  · exact hid_c73 n2 hl hh
  · exact hid_c74 n2 hl hh
  · exact hid_c75 n2 hl hh
  · exact hid_c76 n2 hl hh
  · exact hid_c77 n2 hl hh
  · exact hid_c78 n2 hl hh
  · exact hid_c79 n2 hl hh
  · exact hid_c80 n2 hl hh
  · exact hid_c81 n2 hl hh
  · exact hid_c82 n2 hl hh
  · exact hid_c83 n2 hl hh
  · exact hid_c84 n2 hl hh
  · exact hid_c85 n2 hl hh
  · exact hid_c86 n2 hl hh
  · exact hid_c87 n2 hl hh
  · exact hid_c88 n2 hl hh
  · exact hid_c89 n2 hl hh
  · exact hid_c90 n2 hl hh
  · exact hid_c91 n2 hl hh
  · exact hid_c92 n2 hl hh
  · exact hid_c93 n2 hl hh
  · exact hid_c94 n2 hl hh
  · exact hid_c95 n2 hl hh


/-! ## 8. Attention value readout (REAL softmax simplex / barycentric bridge).

The genuine attention output of coord `o` is the softmax-weighted readout of the
value projections of the 3 key/value tokens `xk : Fin 3 → (Fin 48 → ℝ)` (each in
the input box, sharing the n1 box hence the value box).  By `softmax_readout_mem`
it lies in the value range `[vLo o, vHi o]` for ANY real score map — so the
genuine scaled Q·K scores of `VitRealAttention` feed it. -/

/-- The 3 key positions are nonempty. -/
theorem fin3_ne : (univ : Finset (Fin 3)).Nonempty := ⟨0, mem_univ 0⟩

/-- Genuine attention readout, coord `o`:  `Σ_k softmax(s)_k · (W_v·n1(xk k))_o`,
    i.e. the softmax-weighted value PROJECTION of each key/value token's BN output. -/
noncomputable def attf (xk : Fin 3 → (Fin 48 → ℝ)) (s : Fin 3 → ℝ) (o : Fin 48) : ℝ :=
  ∑ k, softmax univ s k * vf (n1f (xk k)) o

/-- **Attention box.**  If every key/value token lies in the input box, the
    readout `attf` lies in the value range `[vLo o, vHi o]` — barycentric over the
    value box (each token's value projection is in range via `n1_box`+`value_box`)
    through the REAL softmax simplex (`softmax_readout_mem`). -/
theorem attn_box (xk : Fin 3 → (Fin 48 → ℝ)) (s : Fin 3 → ℝ) (o : Fin 48)
    (hl : ∀ k jj, ((xLo jj:ℚ):ℝ) ≤ xk k jj)
    (hh : ∀ k jj, xk k jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((vLo o:ℚ):ℝ) ≤ attf xk s o ∧ attf xk s o ≤ ((vHi o:ℚ):ℝ) := by
  apply softmax_readout_mem (univ : Finset (Fin 3)) s (fun k => vf (n1f (xk k)) o)
    ((vLo o:ℚ):ℝ) ((vHi o:ℚ):ℝ) fin3_ne
  · intro k _
    exact (value_box (n1f (xk k)) (fun jj => (n1_box (xk k) (hl k) (hh k) jj).1)
      (fun jj => (n1_box (xk k) (hl k) (hh k) jj).2) o).1
  · intro k _
    exact (value_box (n1f (xk k)) (fun jj => (n1_box (xk k) (hl k) (hh k) jj).1)
      (fun jj => (n1_box (xk k) (hl k) (hh k) jj).2) o).2

/-! ## 9. ReLU box (the MLP nonlinearity). -/

/-- Genuine post-ReLU activation, coord `o`. -/
noncomputable def rlf (h : Fin 96 → ℝ) (o : Fin 96) : ℝ := reluR (h o)

/-- **ReLU box** (all 96 coords): `rLo o ≤ reluR (h o) ≤ rHi o` from the hidden box,
    using `rLo o = max 0 (hLo o)`, `rHi o = max 0 (hHi o)` (REAL ReLU is monotone). -/
theorem rl_box (h : Fin 96 → ℝ) (hl : ∀ jj, ((hLo jj:ℚ):ℝ) ≤ h jj) (hh : ∀ jj, h jj ≤ ((hHi jj:ℚ):ℝ)) :
    ∀ o, ((rLo o:ℚ):ℝ) ≤ rlf h o ∧ rlf h o ≤ ((rHi o:ℚ):ℝ) := by
  intro o
  have hb := reluR_box ((hLo o:ℚ):ℝ) ((hHi o:ℚ):ℝ) (h o) (hl o) (hh o)
  constructor
  · refine le_trans ?_ hb.1
    -- (rLo o : ℝ) ≤ max 0 (hLo o)  since rLo o = max 0 (hLo o) (exact)
    have : ((rLo o:ℚ):ℝ) = max 0 ((hLo o:ℚ):ℝ) := by
      fin_cases o <;> (simp only [rLo, hLo]; push_cast; norm_num [max_def])
    rw [this]
  · refine le_trans hb.2 ?_
    have : ((rHi o:ℚ):ℝ) = max 0 ((hHi o:ℚ):ℝ) := by
      fin_cases o <;> (simp only [rHi, hHi]; push_cast; norm_num [max_def])
    rw [this]

/-! ## 10. MLP output box (DSL coords). -/

/-- **MLP output box** (DSL coords) from the ReLU box. -/
theorem m_box (rl : Fin 96 → ℝ) (hl : ∀ jj, ((rLo jj:ℚ):ℝ) ≤ rl jj) (hh : ∀ jj, rl jj ≤ ((rHi jj:ℚ):ℝ)) :

    ((mLo 0:ℚ):ℝ) ≤ mf rl 0 ∧ mf rl 0 ≤ ((mHi 0:ℚ):ℝ) := by
  unfold mf
  show ((mLo 0:ℚ):ℝ) ≤ ((b2vv 0:ℚ):ℝ) + ∑ p, ((W2Row 0 p:ℚ):ℝ) * rl p ∧ _
  simp only [b2vv, W2Row, Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact mlp_c0 rl hl hh


/-! ## 11. The genuine block: residuals + threading, and the BLOCK-OUTPUT BOUND.

`x`  = query token (block input), in the input box.
`xk` = 3 key/value tokens, each in the input box (self-attention slice).
`s`  = any real score map (e.g. the genuine scaled Q·K scores of VitRealAttention).

    att o = attf xk s o                 -- attention readout (softmax over values)
    y   o = aof att o + x o             -- attention out-proj (W_o) + RESIDUAL 1
    n2  o = n2f y o                     -- BatchNorm 2
    h   o = hf n2 o                     -- MLP in (W1)
    rl  o = reluR (h o)                 -- ReLU
    m   o = mf rl o                     -- MLP out (W2)
    z   o = m o + y o                   -- RESIDUAL 2  ==  BLOCK OUTPUT
-/

/-- Genuine residual-1 stream, coord `o`:  `aof att o + x o`. -/
noncomputable def yf (x : Fin 48 → ℝ) (att : Fin 48 → ℝ) (o : Fin 48) : ℝ := aof att o + x o

/-- Genuine block output, coord `o`:  `mf rl o + y o`  (RESIDUAL 2). -/
noncomputable def zf (y : Fin 48 → ℝ) (rl : Fin 96 → ℝ) (o : Fin 48) : ℝ := mf rl o + y o

/-- **Residual-1 box** (all 48 coords): `yLo o ≤ aof att o + x o ≤ yHi o`, from the
    attention-out box and the input box (the rounded `[yLo,yHi]` encloses the sum). -/
theorem y_box (x att : Fin 48 → ℝ)
    (hax : ∀ jj, ((aoLo jj:ℚ):ℝ) ≤ aof att jj) (hax' : ∀ jj, aof att jj ≤ ((aoHi jj:ℚ):ℝ))
    (hx : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hx' : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ)) :
    ∀ o, ((yLo o:ℚ):ℝ) ≤ yf x att o ∧ yf x att o ≤ ((yHi o:ℚ):ℝ) := by
  intro o; unfold yf
  have ha := hax o; have ha' := hax' o; have hb := hx o; have hb' := hx' o
  refine ⟨?_, ?_⟩
  · have he : ((yLo o:ℚ):ℝ) ≤ ((aoLo o:ℚ):ℝ) + ((xLo o:ℚ):ℝ) := by
      fin_cases o <;> (simp only [yLo, aoLo, xLo]; push_cast; norm_num)
    linarith [ha, hb, he]
  · have he : ((aoHi o:ℚ):ℝ) + ((xHi o:ℚ):ℝ) ≤ ((yHi o:ℚ):ℝ) := by
      fin_cases o <;> (simp only [yHi, aoHi, xHi]; push_cast; norm_num)
    linarith [ha', hb', he]

/-- **The block-output bound** (DSL coord). -/
theorem block_bound (x : Fin 48 → ℝ) (xk : Fin 3 → (Fin 48 → ℝ)) (s : Fin 3 → ℝ)
    (hx : ∀ jj, ((xLo jj:ℚ):ℝ) ≤ x jj) (hx' : ∀ jj, x jj ≤ ((xHi jj:ℚ):ℝ))
    (hk : ∀ k jj, ((xLo jj:ℚ):ℝ) ≤ xk k jj) (hk' : ∀ k jj, xk k jj ≤ ((xHi jj:ℚ):ℝ)) :
    ((zLo 0:ℚ):ℝ) ≤ zf (yf x (attf xk s)) (rlf (hf (n2f (yf x (attf xk s))))) 0
      ∧ zf (yf x (attf xk s)) (rlf (hf (n2f (yf x (attf xk s))))) 0 ≤ ((zHi 0:ℚ):ℝ) := by
  -- attention box (per coord)
  have hatt : ∀ o, ((vLo o:ℚ):ℝ) ≤ attf xk s o ∧ attf xk s o ≤ ((vHi o:ℚ):ℝ) :=
    fun o => attn_box xk s o hk hk'
  -- attention out-proj box
  have hao : ∀ o, ((aoLo o:ℚ):ℝ) ≤ aof (attf xk s) o ∧ aof (attf xk s) o ≤ ((aoHi o:ℚ):ℝ) :=
    ao_box (attf xk s) (fun jj => (hatt jj).1) (fun jj => (hatt jj).2)
  -- residual-1 box
  have hy : ∀ o, ((yLo o:ℚ):ℝ) ≤ yf x (attf xk s) o ∧ yf x (attf xk s) o ≤ ((yHi o:ℚ):ℝ) :=
    y_box x (attf xk s) (fun jj => (hao jj).1) (fun jj => (hao jj).2) hx hx'
  -- BN2 box
  have hn2 : ∀ o, ((n2Lo o:ℚ):ℝ) ≤ n2f (yf x (attf xk s)) o ∧ n2f (yf x (attf xk s)) o ≤ ((n2Hi o:ℚ):ℝ) :=
    n2_box (yf x (attf xk s)) (fun jj => (hy jj).1) (fun jj => (hy jj).2)
  -- MLP hidden box
  have hh2 : ∀ o, ((hLo o:ℚ):ℝ) ≤ hf (n2f (yf x (attf xk s))) o ∧ hf (n2f (yf x (attf xk s))) o ≤ ((hHi o:ℚ):ℝ) :=
    h_box (n2f (yf x (attf xk s))) (fun jj => (hn2 jj).1) (fun jj => (hn2 jj).2)
  -- ReLU box
  have hrl : ∀ o, ((rLo o:ℚ):ℝ) ≤ rlf (hf (n2f (yf x (attf xk s)))) o ∧ rlf (hf (n2f (yf x (attf xk s)))) o ≤ ((rHi o:ℚ):ℝ) :=
    rl_box (hf (n2f (yf x (attf xk s)))) (fun jj => (hh2 jj).1) (fun jj => (hh2 jj).2)
  -- MLP output box (DSL coord)
  have hm := m_box (rlf (hf (n2f (yf x (attf xk s))))) (fun jj => (hrl jj).1) (fun jj => (hrl jj).2)
  -- RESIDUAL 2: z o0 = m o0 + y o0
  unfold zf
  have hyo := hy 0
  refine ⟨?_, ?_⟩
  · have he : ((zLo 0:ℚ):ℝ) ≤ ((mLo 0:ℚ):ℝ) + ((yLo 0:ℚ):ℝ) := by
      simp only [zLo, mLo, yLo]; push_cast; norm_num
    linarith [hm.1, hyo.1, he]
  · have he : ((mHi 0:ℚ):ℝ) + ((yHi 0:ℚ):ℝ) ≤ ((zHi 0:ℚ):ℝ) := by
      simp only [zHi, mHi, yHi]; push_cast; norm_num
    linarith [hm.2, hyo.2, he]

/-! ## 12. Trust-base check.  MUST be [propext, Classical.choice, Quot.sound]. -/

#print axioms term_boundR
#print axioms dot_ibpR
#print axioms reluR_box
#print axioms rsqrt_enclose
#print axioms prod_interval_R
#print axioms bn_channel_box
#print axioms n1_box
#print axioms value_box
#print axioms ao_box
#print axioms n2_box
#print axioms h_box
#print axioms attn_box
#print axioms rl_box
#print axioms m_box
#print axioms y_box
#print axioms block_bound

end Crownproof.VitFullBlock
