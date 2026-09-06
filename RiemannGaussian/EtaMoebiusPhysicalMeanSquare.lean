import RiemannGaussian.EtaMoebiusPhysicalFamily

/-!
# Mean-square cancellation for the original completed divisor terms

The common physical-cutoff error transports the checked endpoint-family
estimate to the unmodified completed Möbius terms. Their original complex
Gram and exact normalization difference remain upstream. The resulting
bound has the physical decay `A^(-2 Re rho)` and keeps the cubic family
restriction; it is not the original current's uniform weighted bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Mean square of the original family with only the common physical
power attached to its entire sum. -/
def pairedEtaCompletedMoebiusPhysicalMeanSquare (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ r ∈ Finset.range L,
    ‖((A + r : ℕ) : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho (A + r) D‖ ^ 2) / L

/-- Mean square of the unmodified original completed divisor family. -/
def pairedEtaCompletedMoebiusOriginalMeanSquare (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ r ∈ Finset.range L, ‖pairedEtaCompletedMoebiusPartialAggregate rho (A + r) D‖ ^ 2) / L

/-- The physical normalization error gives a pointwise square bound
uniform across the actual averaging window. -/
theorem pairedEtaCompletedMoebiusPartialAggregate_physical_sq_le
    (rho : NontrivialZetaZero) {A M D : ℕ} (hA : 1 ≤ A) (hAM : A ≤ M) (hDA : D ≤ A) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D‖ ^ 2 ≤
      2 * ‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ ^ 2 +
        2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
  let B := pairedEtaCompletedMoebiusPhysicalErrorConstant rho
  have hB : 0 ≤ B := pairedEtaCompletedMoebiusPhysicalErrorConstant_nonneg rho
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have he : ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D -
      pairedEtaCompletedMoebiusEndpointFamily rho M D‖ ≤ B * (D : ℝ) ^ 2 / A := by
    apply (norm_pairedEtaCompletedMoebiusPartialAggregate_physical_sub_endpoint_le rho
      (hDA.trans hAM)).trans
    exact div_le_div_of_nonneg_left (by positivity) hAR (by exact_mod_cast hAM)
  have hz := (norm_le_insert'
    ((M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D)
    (pairedEtaCompletedMoebiusEndpointFamily rho M D)).trans (add_le_add le_rfl he)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz
  have hh := sq_nonneg (‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ - B * (D : ℝ) ^ 2 / A)
  calc
    _ ≤ 2 * ‖pairedEtaCompletedMoebiusEndpointFamily rho M D‖ ^ 2 +
        2 * (B * (D : ℝ) ^ 2 / A) ^ 2 := by nlinarith
    _ = _ := by dsimp [B]; ring

/-- The common physical normalization transports the family mean-square
bound with one explicit quadratic normalization error. -/
theorem pairedEtaCompletedMoebiusPhysicalMeanSquare_le_endpoint
    (rho : NontrivialZetaZero) {A L D : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (hDA : D ≤ A) :
    pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D ≤
      2 * pairedEtaCompletedMoebiusFamilyMeanSquare rho A L D +
        2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  unfold pairedEtaCompletedMoebiusPhysicalMeanSquare
  calc
    _ ≤ (∑ r ∈ Finset.range L,
        (2 * ‖pairedEtaCompletedMoebiusEndpointFamily rho (A + r) D‖ ^ 2 +
          2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2)) / (L : ℝ) := by
      apply div_le_div_of_nonneg_right _ hLR.le
      apply Finset.sum_le_sum
      intro r hr
      exact pairedEtaCompletedMoebiusPartialAggregate_physical_sq_le rho hA (by omega) hDA
    _ = _ := by
      unfold pairedEtaCompletedMoebiusFamilyMeanSquare
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- The explicit family constant after removing all individual
endpoint powers from the original completed terms. -/
def pairedEtaCompletedMoebiusOriginalFamilyConstant (rho : NontrivialZetaZero) : ℝ :=
  2 * pairedEtaCompletedMoebiusFamilyBoundConstant rho +
    2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2

/-- The completion-dependent original-family constant is nonnegative. -/
theorem pairedEtaCompletedMoebiusOriginalFamilyConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedMoebiusOriginalFamilyConstant rho := by
  have h := pairedEtaCompletedMoebiusFamilyBoundConstant_nonneg rho
  unfold pairedEtaCompletedMoebiusOriginalFamilyConstant
  positivity

/-- The original divisor family with a common physical power has a
linear logarithmic mean square in the proved cubic range. -/
theorem pairedEtaCompletedMoebiusPhysicalMeanSquare_le_growing
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 3 ≤ A) (hDL : D ^ 3 ≤ L) :
    pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusOriginalFamilyConstant rho * D * (1 + Real.log D) := by
  have hDp : 0 < D ^ 3 := pow_pos hD _
  have hDD : D ≤ D ^ 3 := Nat.le_self_pow (by omega) D
  have hA : 1 ≤ A := hD.trans (hDD.trans hDA)
  have hL : 0 < L := hDp.trans_le hDL
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hDAR : (D : ℝ) ^ 3 ≤ A := by exact_mod_cast hDA
  have hlog : 1 ≤ 1 + Real.log D := by linarith [Real.log_nonneg hDR]
  have herror : (D : ℝ) ^ 4 / (A : ℝ) ^ 2 ≤ D := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (A : ℝ) ^ 2)).mpr
    have hAA : (A : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (hDAR.trans hAA) (Nat.cast_nonneg (α := ℝ) D)]
  have he := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ 2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2)
  have helog := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ 2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2 * D)
  have hmain := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusFamilyMeanSquare_le_growing rho hD hDA hDL)
    (by norm_num : (0 : ℝ) ≤ 2)
  apply (pairedEtaCompletedMoebiusPhysicalMeanSquare_le_endpoint rho hA hL (hDD.trans hDA)).trans
  unfold pairedEtaCompletedMoebiusOriginalFamilyConstant
  simp only [← mul_div_assoc] at he
  nlinarith

/-- Removing the common physical power leaves the original zero's
exact decay exponent, uniformly across the whole averaging window. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_le_physical
    (rho : NontrivialZetaZero) {A : ℕ} (hA : 1 ≤ A) (L D : ℕ) :
    pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D ≤
      (A : ℝ) ^ (-2 * rho.1.re) * pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  unfold pairedEtaCompletedMoebiusOriginalMeanSquare pairedEtaCompletedMoebiusPhysicalMeanSquare
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  apply Finset.sum_le_sum
  intro r hr
  rw [pairedEtaCompletedMoebiusPartialAggregate_norm_sq_eq_physical rho (by omega)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hAR (by exact_mod_cast (Nat.le_add_right A r))
    (by linarith [NontrivialZetaZero.zero_lt_re rho])

/-- The unmodified completed Möbius family has a mean-square bound with
its original physical decay and an explicit growing divisor cutoff. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_le_growing
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 3 ≤ A) (hDL : D ^ 3 ≤ L) :
    pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusOriginalFamilyConstant rho * D * (1 + Real.log D) *
        (A : ℝ) ^ (-2 * rho.1.re) := by
  have hA : 1 ≤ A := (pow_pos hD 3).trans_le hDA
  apply (pairedEtaCompletedMoebiusOriginalMeanSquare_le_physical rho hA L D).trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusPhysicalMeanSquare_le_growing rho hD hDA hDL)
    (Real.rpow_nonneg (Nat.cast_nonneg A) (-2 * rho.1.re))
  convert h using 1
  ring

end

end RiemannGaussian
