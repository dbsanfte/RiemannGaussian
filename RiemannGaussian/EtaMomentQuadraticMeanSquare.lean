import RiemannGaussian.EtaMomentPhysicalFamily

/-!
# Quadratic divisor bounds for the actual moving-center moments

The original moment family uses the next physical logarithmic endpoint as
its moving center. Its complete complex reduction to the zeroth-order
family transports the proved Fourier mean-square estimate, with all
moment, completion, physical decay, and divisor-range costs explicit.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The actual moment family's mean square with its common physical power. -/
def pairedEtaCompletedMomentPhysicalMeanSquare (rho : NontrivialZetaZero) (k A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖((A + n : ℕ) : ℂ) ^ rho.1 *
    pairedEtaCompletedMomentOriginalFamily rho k (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) D‖ ^ 2) / L

/-- The mean square of the unmodified moment family at the actual moving center. -/
def pairedEtaCompletedMomentOriginalMeanSquare (rho : NontrivialZetaZero) (k A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L,
    ‖pairedEtaCompletedMomentOriginalFamily rho k (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) D‖ ^ 2) / L

/-- The actual family square is bounded after retaining the complex
moment reduction and the full zeroth-order physical family. -/
theorem pairedEtaCompletedMomentOriginalFamily_physical_sq_le
    (rho : NontrivialZetaZero) {k A M D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hA : 1 ≤ A) (hAM : A ≤ M) (hDA : D ≤ A) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentOriginalFamily rho k a M D‖ ^ 2 ≤
      2 * ‖pairedEtaMomentParityCoefficient rho k‖ ^ 2 *
        ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D‖ ^ 2 +
      2 * pairedEtaCompletedMomentPhysicalErrorConstant rho k ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
  let B := pairedEtaCompletedMomentPhysicalErrorConstant rho k
  have hB : 0 ≤ B := pairedEtaCompletedMomentPhysicalErrorConstant_nonneg rho k
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have he : ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentOriginalFamily rho k a M D -
      pairedEtaMomentParityCoefficient rho k *
        ((M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D)‖ ≤ B * (D : ℝ) ^ 2 / A := by
    rw [show (M : ℂ) ^ rho.1 * pairedEtaCompletedMomentOriginalFamily rho k a M D -
      pairedEtaMomentParityCoefficient rho k *
        ((M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D) =
      (M : ℂ) ^ rho.1 * (pairedEtaCompletedMomentOriginalFamily rho k a M D -
        pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusPartialAggregate rho M D) by ring]
    apply (norm_pairedEtaCompletedMomentOriginalFamily_physical_sub_zero_le rho hk (hDA.trans hAM) ha).trans
    exact div_le_div_of_nonneg_left (by positivity) hAR (by exact_mod_cast hAM)
  have hz := (norm_le_insert' ((M : ℂ) ^ rho.1 * pairedEtaCompletedMomentOriginalFamily rho k a M D)
    (pairedEtaMomentParityCoefficient rho k *
      ((M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D))).trans
        (add_le_add le_rfl he)
  rw [norm_mul (pairedEtaMomentParityCoefficient rho k)] at hz
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz
  have hh := sq_nonneg (‖pairedEtaMomentParityCoefficient rho k‖ *
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D‖ - B * (D : ℝ) ^ 2 / A)
  calc
    _ ≤ 2 * ‖pairedEtaMomentParityCoefficient rho k‖ ^ 2 *
        ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho M D‖ ^ 2 +
          2 * (B * (D : ℝ) ^ 2 / A) ^ 2 := by nlinarith
    _ = _ := by dsimp [B]; ring

/-- The actual moving-center mean square transports from the checked
zeroth-order physical family, with the full moment coefficient and error. -/
theorem pairedEtaCompletedMomentPhysicalMeanSquare_le_zero
    (rho : NontrivialZetaZero) {k A L D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hA : 1 ≤ A) (hL : 0 < L) (hDA : D ≤ A) :
    pairedEtaCompletedMomentPhysicalMeanSquare rho k A L D ≤
      2 * ‖pairedEtaMomentParityCoefficient rho k‖ ^ 2 * pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D +
      2 * pairedEtaCompletedMomentPhysicalErrorConstant rho k ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  unfold pairedEtaCompletedMomentPhysicalMeanSquare
  calc
    _ ≤ (∑ n ∈ Finset.range L,
        (2 * ‖pairedEtaMomentParityCoefficient rho k‖ ^ 2 *
          ‖((A + n : ℕ) : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusPartialAggregate rho (A + n) D‖ ^ 2 +
        2 * pairedEtaCompletedMomentPhysicalErrorConstant rho k ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2)) / (L : ℝ) := by
      apply div_le_div_of_nonneg_right _ hLR.le
      apply Finset.sum_le_sum
      intro n hn
      have hM : (0 : ℝ) < (A + n : ℕ) := by exact_mod_cast (show 1 ≤ A + n by omega)
      exact pairedEtaCompletedMomentOriginalFamily_physical_sq_le rho hk hA (by omega) hDA
        ⟨Real.log_le_log hM (by linarith), le_rfl⟩
    _ = _ := by
      unfold pairedEtaCompletedMoebiusPhysicalMeanSquare
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- An explicit constant for the original moving-center moment family. -/
def pairedEtaCompletedMomentQuadraticConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  2 * ‖pairedEtaMomentParityCoefficient rho k‖ ^ 2 * pairedEtaCompletedMoebiusOriginalQuadraticConstant rho +
    2 * pairedEtaCompletedMomentPhysicalErrorConstant rho k ^ 2

/-- The moving-center moment constant is nonnegative. -/
theorem pairedEtaCompletedMomentQuadraticConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaCompletedMomentQuadraticConstant rho k := by
  have h := pairedEtaCompletedMoebiusOriginalQuadraticConstant_nonneg rho
  unfold pairedEtaCompletedMomentQuadraticConstant
  positivity

/-- Every actual lower moment has linear logarithmic mean square with
the common physical power throughout the proved quadratic divisor range. -/
theorem pairedEtaCompletedMomentPhysicalMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) {k A L D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hD : 1 ≤ D) (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaCompletedMomentPhysicalMeanSquare rho k A L D ≤
      pairedEtaCompletedMomentQuadraticConstant rho k * D * (1 + Real.log D) := by
  have hA : 1 ≤ A := (pow_pos hD 2).trans_le hDA
  have hL : 0 < L := (pow_pos hD 2).trans_le hDL
  have hDle : D ≤ A := (Nat.le_self_pow (by decide : 2 ≠ 0) D).trans hDA
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlog : 1 ≤ 1 + Real.log D := by linarith [Real.log_nonneg hDR]
  have hcost : 1 ≤ (D : ℝ) * (1 + Real.log D) := by nlinarith
  have he := mul_le_mul_of_nonneg_left
    ((divisor_fourth_div_cutoff_sq_le_one hA hDA).trans hcost)
    (by positivity : 0 ≤ 2 * pairedEtaCompletedMomentPhysicalErrorConstant rho k ^ 2)
  have hm := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusPhysicalMeanSquare_le_quadratic rho hD hDA hDL)
    (by positivity : 0 ≤ 2 * ‖pairedEtaMomentParityCoefficient rho k‖ ^ 2)
  apply (pairedEtaCompletedMomentPhysicalMeanSquare_le_zero rho hk hA hL hDle).trans
  unfold pairedEtaCompletedMomentQuadraticConstant
  simp only [← mul_div_assoc] at he
  nlinarith

/-- Removing the common physical power keeps the original zero's
horizontal decay for the entire moving-center moment family. -/
theorem pairedEtaCompletedMomentOriginalMeanSquare_le_physical
    (rho : NontrivialZetaZero) (k : ℕ) {A : ℕ} (hA : 1 ≤ A) (L D : ℕ) :
    pairedEtaCompletedMomentOriginalMeanSquare rho k A L D ≤
      (A : ℝ) ^ (-2 * rho.1.re) * pairedEtaCompletedMomentPhysicalMeanSquare rho k A L D := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  unfold pairedEtaCompletedMomentOriginalMeanSquare pairedEtaCompletedMomentPhysicalMeanSquare
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  apply Finset.sum_le_sum
  intro n hn
  rw [pairedEtaCompletedMomentOriginalFamily_norm_sq_eq_physical rho k _ (by omega)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hAR (by exact_mod_cast (Nat.le_add_right A n))
    (by linarith [NontrivialZetaZero.zero_lt_re rho])

/-- The unmodified moment family at the actual moving center has
physical mean-square decay for every order below the actual zero's full
multiplicity, throughout the quadratic divisor range. -/
theorem pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) {k A L D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hD : 1 ≤ D) (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaCompletedMomentOriginalMeanSquare rho k A L D ≤
      pairedEtaCompletedMomentQuadraticConstant rho k * D * (1 + Real.log D) *
        (A : ℝ) ^ (-2 * rho.1.re) := by
  have hA : 1 ≤ A := (pow_pos hD 2).trans_le hDA
  apply (pairedEtaCompletedMomentOriginalMeanSquare_le_physical rho k hA L D).trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMomentPhysicalMeanSquare_le_quadratic rho hk hD hDA hDL)
    (Real.rpow_nonneg (Nat.cast_nonneg A) (-2 * rho.1.re))
  convert h using 1
  ring

end

end RiemannGaussian
