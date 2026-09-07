import RiemannGaussian.EtaRationalTranslateGram
import RiemannGaussian.EtaCurrentTranslatedProjectionPower
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Four explicit eta translates with a full residual budget below one fifth

The coefficient search suggests the rational physical scales
`1/4, 1/2, 3/4, 1` with coefficients `-1/2, -1/2, 1/2, 1`.
The finite interval Gram and full tail at the original cutoff `N=64`
are checked by rational kernel reduction. The target pairing retains its
exact logarithms. The resulting bound concerns the complete continuous
residual and is available for both branches of the original current.
-/

open Complex Set

namespace RiemannGaussian

/-- Four rational physical scales, including two internal and two endpoint translates. -/
def pairedEtaFourProjectionScale : Fin 4 → ℚ := ![1 / 4, 1 / 2, 3 / 4, 1]

/-- The explicit signed rational coefficients found by the finite full-budget search. -/
def pairedEtaFourProjectionCoefficient : Fin 4 → ℚ := ![-(1 / 2), -(1 / 2), 1 / 2, 1]

/-- Every selected physical scale belongs to the original allowed interval. -/
theorem pairedEtaFourProjectionScale_bounds (j : Fin 4) :
    0 < pairedEtaFourProjectionScale j ∧ pairedEtaFourProjectionScale j ≤ 1 := by
  fin_cases j <;> norm_num [pairedEtaFourProjectionScale]

-- Check entries in separate serial commands to keep kernel reduction within CI memory.
set_option Elab.async false

/-- Rational overlap symmetry reuses each off-diagonal calculation. -/
private theorem fourGram_symm (N : ℕ) (r s : ℚ) :
    pairedEtaRationalFiniteGram N r s = pairedEtaRationalFiniteGram N s r := by
  unfold pairedEtaRationalFiniteGram
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  simp only [pairedEtaRationalOverlapMass, min_comm, max_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first exact diagonal entry, checked separately by kernel reduction. -/
private theorem fourGram11 : pairedEtaRationalFiniteGram 64 (1 / 4) (1 / 4) =
    13981692518567 / 82516315939200 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact first/second overlap, including all original interval pairs. -/
private theorem fourGram12 : pairedEtaRationalFiniteGram 64 (1 / 4) (1 / 2) =
    29294219493288391 / 474994075682206080 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact first/third overlap, including all original interval pairs. -/
private theorem fourGram13 : pairedEtaRationalFiniteGram 64 (1 / 4) (3 / 4) =
    428200027754758225632107339 / 3650933388916848810846470400 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact first/fourth overlap, including all original interval pairs. -/
private theorem fourGram14 : pairedEtaRationalFiniteGram 64 (1 / 4) 1 =
    2405424323434643403921696807250126559 / 33274220144429173657870601889057648000 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second exact diagonal entry, checked separately by kernel reduction. -/
private theorem fourGram22 : pairedEtaRationalFiniteGram 64 (1 / 2) (1 / 2) =
    810320648392931898373256717 / 2364533768205644535022723200 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact second/third overlap, including all original interval pairs. -/
private theorem fourGram23 : pairedEtaRationalFiniteGram 64 (1 / 2) (3 / 4) =
    1058916174834192282988908488393 / 6079135182094077592132905861600 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact second/fourth overlap, including all original interval pairs. -/
private theorem fourGram24 : pairedEtaRationalFiniteGram 64 (1 / 2) 1 =
    10021705556251774594922810149728761 / 80025791590465929269378289609436800 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The third exact diagonal entry, checked separately by kernel reduction. -/
private theorem fourGram33 : pairedEtaRationalFiniteGram 64 (3 / 4) (3 / 4) =
    98897413912101176502959976158939147221 / 191671134652130521414525935217353411840 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact third/fourth overlap, including all original interval pairs. -/
private theorem fourGram34 : pairedEtaRationalFiniteGram 64 (3 / 4) 1 =
    7028695778647326393298286831573909148331 / 22946493971249170405062710720659461792000 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The fourth exact diagonal entry, checked separately by kernel reduction. -/
private theorem fourGram44 : pairedEtaRationalFiniteGram 64 1 1 =
    9204159030559409899503223815970003359186125226214526531 /
      13353756090997411579403749204440236542538872688049072000 := by decide +kernel

/-- The entire rational quadratic Gram and coefficient tail have a strict rational upper bound, assembled from kernel-checked entries. -/
theorem pairedEtaFourProjection_rationalQuadraticBudget_lt :
    pairedEtaRationalQuadraticBudget 64 pairedEtaFourProjectionScale pairedEtaFourProjectionCoefficient < 99 / 100 := by
  have h21 := (fourGram_symm 64 (1 / 2) (1 / 4)).trans fourGram12
  have h31 := (fourGram_symm 64 (3 / 4) (1 / 4)).trans fourGram13
  have h41 := (fourGram_symm 64 1 (1 / 4)).trans fourGram14
  have h32 := (fourGram_symm 64 (3 / 4) (1 / 2)).trans fourGram23
  have h42 := (fourGram_symm 64 1 (1 / 2)).trans fourGram24
  have h43 := (fourGram_symm 64 1 (3 / 4)).trans fourGram34
  norm_num [pairedEtaRationalQuadraticBudget, Fin.sum_univ_succ,
    pairedEtaFourProjectionScale, pairedEtaFourProjectionCoefficient,
    fourGram11, fourGram12, fourGram13, fourGram14, fourGram22, fourGram23,
    fourGram24, fourGram33, fourGram34, fourGram44, h21, h31, h41, h32, h42, h43]

end RiemannGaussian
