import RiemannGaussian.EtaMoebiusFamilyMeanSquare

/-!
# A quantitative growing range for the actual completed divisor family

When both the starting cutoff and averaging length exceed the cube of the
divisor count, all explicit errors fit within a linear logarithmic mean-square
bound. The constant is evaluated in the actual completion factor and endpoint
error coefficient. This is a truncated family estimate, not a bound over the
entire physical divisor range or the original weighted current.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- An explicit constant for the growing completed divisor family. -/
def pairedEtaCompletedMoebiusFamilyBoundConstant (rho : NontrivialZetaZero) : ℝ :=
  2 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 +
  2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * ‖pairedEtaXiCompletionFactor rho.1‖ +
  4 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2

/-- The actual completion-dependent family constant is nonnegative. -/
theorem pairedEtaCompletedMoebiusFamilyBoundConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedMoebiusFamilyBoundConstant rho := by
  have h := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  unfold pairedEtaCompletedMoebiusFamilyBoundConstant
  positivity

/-- In the explicit cubic range, the whole summed completed family has
linear logarithmic mean square. Both the physical cutoff and averaging
length grow with the family, and no simplicity hypothesis is imposed. -/
theorem pairedEtaCompletedMoebiusFamilyMeanSquare_le_growing
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 3 ≤ A) (hDL : D ^ 3 ≤ L) :
    pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusFamilyBoundConstant rho * D * (1 + Real.log D) := by
  have hDp : 0 < D ^ 3 := pow_pos hD _
  have hA : 1 ≤ A := by omega
  have hL : 0 < L := by omega
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hDAR : (D : ℝ) ^ 3 ≤ A := by exact_mod_cast hDA
  have hDLR : (D : ℝ) ^ 3 ≤ L := by exact_mod_cast hDL
  have hH := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  have hlog : 1 ≤ 1 + Real.log D := by linarith [Real.log_nonneg hDR]
  have hwindow : (D : ℝ) ^ 4 / L ≤ D := by
    apply (div_le_iff₀ hLR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hDLR (Nat.cast_nonneg (α := ℝ) D)]
  have hfirst : (D : ℝ) ^ 3 / A ≤ D :=
    ((div_le_one (by linarith : (0 : ℝ) < A)).mpr hDAR).trans hDR
  have hsecond : (D : ℝ) ^ 4 / (A : ℝ) ^ 2 ≤ D := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (A : ℝ) ^ 2)).mpr
    have hAA : (A : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (hDAR.trans hAA) (Nat.cast_nonneg (α := ℝ) D)]
  apply (pairedEtaCompletedMoebiusFamilyMeanSquare_le rho hA hL D).trans
  let C := ‖pairedEtaXiCompletionFactor rho.1‖
  let H := pairedEtaCompletedMoebiusPhaseErrorConstant rho
  have hC : 0 ≤ C := norm_nonneg _
  have hHr : 0 ≤ H := hH
  have hw := mul_le_mul_of_nonneg_left hwindow (sq_nonneg C)
  have hf := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 2 * H * C)
  have hs := mul_le_mul_of_nonneg_left hsecond (by positivity : 0 ≤ 4 * H ^ 2)
  change C ^ 2 / 2 * D * (1 + Real.log D) + C ^ 2 * (D : ℝ) ^ 4 / L +
    2 * H * C * (D : ℝ) ^ 3 / A + 4 * H ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 ≤ _
  have hcost : C ^ 2 / 2 * D * (1 + Real.log D) + C ^ 2 * (D : ℝ) ^ 4 / L +
      2 * H * C * (D : ℝ) ^ 3 / A + 4 * H ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 ≤
      C ^ 2 / 2 * D * (1 + Real.log D) + (C ^ 2 + 2 * H * C + 4 * H ^ 2) * D := by
    simp only [← mul_div_assoc] at hw hf hs
    nlinarith
  apply hcost.trans
  have hq := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ (C ^ 2 + 2 * H * C + 4 * H ^ 2) * D)
  have hmain : 0 ≤ C ^ 2 * D * (1 + Real.log D) := by positivity
  dsimp [pairedEtaCompletedMoebiusFamilyBoundConstant]
  change _ ≤ (2 * C ^ 2 + 2 * H * C + 4 * H ^ 2) * D * (1 + Real.log D)
  nlinarith

end

end RiemannGaussian
