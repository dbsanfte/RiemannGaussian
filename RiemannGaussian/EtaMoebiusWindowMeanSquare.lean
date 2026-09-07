import RiemannGaussian.EtaMoebiusOriginalQuadraticFamily

/-!
# The complete physical-window budget for the original Möbius family

The separated Fourier estimate is retained with its full `4D² + L`
cost. Transport through both original endpoint errors therefore gives a
bound even when `D² > L`. The price is explicit, rather than removing
the divisor range hypothesis from the earlier quadratic corollary.
The original complex family identities remain available upstream.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- The actual parity mean square retains the complete sampling-window loss outside the quadratic range. -/
theorem pairedEtaCompletedMoebiusParityMeanSquare_le_window
    (rho : NontrivialZetaZero) (A : ℕ) {D L : ℕ} (hD : 1 ≤ D) (hL : 0 < L) :
    pairedEtaCompletedMoebiusParityMeanSquare rho A L D ≤
      (finiteCircleSamplingConstant * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2) *
        (((4 * (D : ℝ) ^ 2 + L) / L) * D * (1 + Real.log D)) := by
  apply (div_le_div_of_nonneg_right
    (pairedEtaCompletedMoebiusParityFamily_window_sq_le rho A hD hL) (Nat.cast_nonneg L)).trans_eq
  ring

/-- Both complete endpoint errors and the entire physical-window loss bound the original family with its common physical power still attached. -/
theorem pairedEtaCompletedMoebiusPhysicalMeanSquare_le_window
    (rho : NontrivialZetaZero) {A L D : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hD : 1 ≤ D) (hDA : D ≤ A) :
    pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusOriginalQuadraticConstant rho *
        (((4 * (D : ℝ) ^ 2 + L) / L) * D * (1 + Real.log D) +
          (D : ℝ) ^ 4 / (A : ℝ) ^ 2) := by
  let V := ((4 * (D : ℝ) ^ 2 + L) / L) * D * (1 + Real.log D)
  let E := (D : ℝ) ^ 4 / (A : ℝ) ^ 2
  let K := ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2
  let H := pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2
  let B := pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2
  have hlog : 0 ≤ 1 + Real.log (D : ℝ) := by
    have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith [Real.log_nonneg hd]
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK : 0 ≤ K := sq_nonneg _
  have hmain : 2 * finiteCircleSamplingConstant * K ≤ pairedEtaCompletedMoebiusOriginalQuadraticConstant rho := by
    dsimp [pairedEtaCompletedMoebiusOriginalQuadraticConstant, pairedEtaCompletedMoebiusQuadraticFamilyConstant, K]
    nlinarith [mul_nonneg finiteCircleSamplingConstant_pos.le hK,
      sq_nonneg (pairedEtaCompletedMoebiusPhaseErrorConstant rho),
      sq_nonneg (pairedEtaCompletedMoebiusPhysicalErrorConstant rho)]
  have herr : 16 * H + 2 * B ≤ pairedEtaCompletedMoebiusOriginalQuadraticConstant rho := by
    dsimp [pairedEtaCompletedMoebiusOriginalQuadraticConstant, pairedEtaCompletedMoebiusQuadraticFamilyConstant, H, B]
    nlinarith [mul_nonneg finiteCircleSamplingConstant_pos.le hK]
  have hp := pairedEtaCompletedMoebiusParityMeanSquare_le_window rho A hD hL
  have he := pairedEtaCompletedMoebiusFamilyMeanSquare_le_parity rho hA hL D
  have ho := pairedEtaCompletedMoebiusPhysicalMeanSquare_le_endpoint rho hA hL hDA
  change pairedEtaCompletedMoebiusParityMeanSquare rho A L D ≤
    finiteCircleSamplingConstant * K / 2 * V at hp
  change pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D ≤
    2 * pairedEtaCompletedMoebiusParityMeanSquare rho A L D + 8 * H * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 at he
  change pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D ≤
    2 * pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D + 2 * B * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 at ho
  have he' : pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D ≤
      2 * pairedEtaCompletedMoebiusParityMeanSquare rho A L D + 8 * H * E := by
    simpa only [E, ← mul_div_assoc] using he
  have ho' : pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D ≤
      2 * pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D + 2 * B * E := by
    simpa only [E, ← mul_div_assoc] using ho
  calc
    _ ≤ (2 * finiteCircleSamplingConstant * K) * V + (16 * H + 2 * B) * E := by nlinarith
    _ ≤ pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * V +
        pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * E :=
      add_le_add (mul_le_mul_of_nonneg_right hmain hV) (mul_le_mul_of_nonneg_right herr hE)
    _ = _ := by dsimp [V, E]; ring

/-- The unmodified completed Möbius aggregate has its original physical decay with all divisor, window, and endpoint costs explicit; no quadratic-window hypothesis is imposed. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_le_window
    (rho : NontrivialZetaZero) {A L D : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hD : 1 ≤ D) (hDA : D ≤ A) :
    pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusOriginalQuadraticConstant rho *
        (((4 * (D : ℝ) ^ 2 + L) / L) * D * (1 + Real.log D) +
          (D : ℝ) ^ 4 / (A : ℝ) ^ 2) * (A : ℝ) ^ (-2 * rho.1.re) := by
  apply (pairedEtaCompletedMoebiusOriginalMeanSquare_le_physical rho hA L D).trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusPhysicalMeanSquare_le_window rho hA hL hD hDA)
    (Real.rpow_nonneg (Nat.cast_nonneg A) (-2 * rho.1.re))
  simpa only [mul_comm] using h

end

end RiemannGaussian
