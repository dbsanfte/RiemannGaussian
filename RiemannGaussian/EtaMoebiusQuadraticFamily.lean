import RiemannGaussian.EtaMoebiusParitySampling
import RiemannGaussian.EtaMoebiusPhysicalMeanSquare

/-!
# The quadratic range for the actual completed endpoint family

The exact complex family error transports the proved parity sampling
estimate through the literal physical endpoints. Its square cost fits in
the linear logarithmic family budget when both the starting cutoff and
window length exceed the square of the divisor count.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The family error retains every completed complex endpoint correction
and the corresponding literal quotient phase. -/
theorem pairedEtaCompletedMoebiusEndpointFamily_sub_parity
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaCompletedMoebiusEndpointFamily rho M D -
      pairedEtaCompletedMoebiusParityFamily rho M D =
        ∑ d ∈ Finset.Icc 1 D, (pairedEtaCompletedMoebiusEndpointPhase rho M d -
          pairedEtaCompletedMoebiusParityPhase rho M d) := by
  simp only [pairedEtaCompletedMoebiusEndpointFamily, pairedEtaCompletedMoebiusParityFamily,
    Finset.sum_sub_distrib]

/-- The exact summed endpoint correction has a square-scale divisor
bound at the original physical cutoff. -/
theorem norm_pairedEtaCompletedMoebiusEndpointFamily_sub_parity_le
    (rho : NontrivialZetaZero) {M : ℕ} (hM : 1 ≤ M) (D : ℕ) :
    ‖pairedEtaCompletedMoebiusEndpointFamily rho M D -
      pairedEtaCompletedMoebiusParityFamily rho M D‖ ≤
        2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * (D : ℝ) ^ 2 / M := by
  rw [pairedEtaCompletedMoebiusEndpointFamily_sub_parity]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 D,
        2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho * D / (M : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le rho hM
        (Finset.mem_Icc.mp hd).1).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
        (mul_nonneg (by norm_num) (pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho))
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- The full endpoint family's square is controlled by the original
parity-family square and the explicit physical endpoint error. -/
theorem pairedEtaCompletedMoebiusEndpointFamily_sq_le_parity
    (rho : NontrivialZetaZero) {A M : ℕ} (hA : 1 ≤ A) (hAM : A ≤ M) (D : ℕ) :
    ‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ ^ 2 ≤
      2 * ‖pairedEtaCompletedMoebiusParityFamily rho M D‖ ^ 2 +
        8 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
  let H := pairedEtaCompletedMoebiusPhaseErrorConstant rho
  have hH : 0 ≤ H := pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have he : ‖pairedEtaCompletedMoebiusEndpointFamily rho M D -
      pairedEtaCompletedMoebiusParityFamily rho M D‖ ≤ 2 * H * (D : ℝ) ^ 2 / A := by
    apply (norm_pairedEtaCompletedMoebiusEndpointFamily_sub_parity_le rho (hA.trans hAM) D).trans
    exact div_le_div_of_nonneg_left (by positivity) hAR (by exact_mod_cast hAM)
  have hz := (norm_le_insert' (pairedEtaCompletedMoebiusEndpointFamily rho M D)
    (pairedEtaCompletedMoebiusParityFamily rho M D)).trans (add_le_add le_rfl he)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz
  have hh := sq_nonneg (‖pairedEtaCompletedMoebiusParityFamily rho M D‖ - 2 * H * (D : ℝ) ^ 2 / A)
  calc
    _ ≤ 2 * ‖pairedEtaCompletedMoebiusParityFamily rho M D‖ ^ 2 +
        2 * (2 * H * (D : ℝ) ^ 2 / A) ^ 2 := by nlinarith
    _ = _ := by dsimp [H]; ring

/-- The literal endpoint mean square transports from the parity estimate
with an explicit fourth-power divisor error over the squared physical cutoff. -/
theorem pairedEtaCompletedMoebiusFamilyMeanSquare_le_parity
    (rho : NontrivialZetaZero) {A L : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (D : ℕ) :
    pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D ≤
      2 * pairedEtaCompletedMoebiusParityMeanSquare rho A L D +
        8 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  unfold pairedEtaCompletedMoebiusFamilyMeanSquare
  calc
    _ ≤ (∑ n ∈ Finset.range L,
        (2 * ‖pairedEtaCompletedMoebiusParityFamily rho (A + n) D‖ ^ 2 +
          8 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2)) / (L : ℝ) := by
      apply div_le_div_of_nonneg_right _ hLR.le
      apply Finset.sum_le_sum
      intro n hn
      exact pairedEtaCompletedMoebiusEndpointFamily_sq_le_parity rho hA (by omega) D
    _ = _ := by
      unfold pairedEtaCompletedMoebiusParityMeanSquare
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- A quadratic divisor cutoff makes the fourth-power normalization
error at most one, with a strictly positive physical denominator. -/
theorem divisor_fourth_div_cutoff_sq_le_one {D A : ℕ} (hA : 1 ≤ A) (hDA : D ^ 2 ≤ A) :
    (D : ℝ) ^ 4 / (A : ℝ) ^ 2 ≤ 1 := by
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hDAR : (D : ℝ) ^ 2 ≤ A := by exact_mod_cast hDA
  apply (div_le_one (by positivity : (0 : ℝ) < (A : ℝ) ^ 2)).mpr
  nlinarith [sq_le_sq₀ (sq_nonneg (D : ℝ)) (by positivity : (0 : ℝ) ≤ A)]

/-- An explicit completion-dependent constant for the quadratic family range. -/
def pairedEtaCompletedMoebiusQuadraticFamilyConstant (rho : NontrivialZetaZero) : ℝ :=
  5 * finiteCircleSamplingConstant * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 +
    8 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2

/-- The quadratic family constant is nonnegative. -/
theorem pairedEtaCompletedMoebiusQuadraticFamilyConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedMoebiusQuadraticFamilyConstant rho := by
  have h := finiteCircleSamplingConstant_pos
  unfold pairedEtaCompletedMoebiusQuadraticFamilyConstant
  positivity

/-- The literal completed endpoint family has linear logarithmic mean
square throughout the quadratic range, with every analytic premise discharged. -/
theorem pairedEtaCompletedMoebiusFamilyMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusQuadraticFamilyConstant rho * D * (1 + Real.log D) := by
  have hA : 1 ≤ A := (pow_pos hD 2).trans_le hDA
  have hL : 0 < L := (pow_pos hD 2).trans_le hDL
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlog : 1 ≤ 1 + Real.log D := by linarith [Real.log_nonneg hDR]
  have hcost : 1 ≤ (D : ℝ) * (1 + Real.log D) := by nlinarith
  have he := mul_le_mul_of_nonneg_left
    ((divisor_fourth_div_cutoff_sq_le_one hA hDA).trans hcost)
    (by positivity : 0 ≤ 8 * pairedEtaCompletedMoebiusPhaseErrorConstant rho ^ 2)
  have hm := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusParityMeanSquare_le_quadratic rho A hD hDL)
    (by norm_num : (0 : ℝ) ≤ 2)
  apply (pairedEtaCompletedMoebiusFamilyMeanSquare_le_parity rho hA hL D).trans
  unfold pairedEtaCompletedMoebiusQuadraticFamilyConstant
  simp only [← mul_div_assoc] at he
  nlinarith

end

end RiemannGaussian
