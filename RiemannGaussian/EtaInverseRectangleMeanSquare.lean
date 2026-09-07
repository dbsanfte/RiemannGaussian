import RiemannGaussian.EtaMomentInverseRectangle

/-!
# Joint mean-square control of the actual completed inverse rectangle

Both original divisor sums are estimated together at the moving physical
center. Exact product grouping, the collision-energy estimate, the proved
Fourier support, and the full atom normalization error are all discharged
before the mean-square bound is transferred to the unmodified inverse.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The explicit area and logarithmic energy cost of the two divisor ranges. -/
def pairedEtaInverseRectangleBudget (E D : ℕ) : ℝ :=
  ((E : ℝ) * D) * (1 + Real.log E) ^ 2 * (1 + Real.log (E * D : ℕ)) ^ 2

/-- Every nonempty positive rectangle has an energy budget at least one. -/
theorem one_le_pairedEtaInverseRectangleBudget {E D : ℕ} (hE : 1 ≤ E) (hD : 1 ≤ D) :
    1 ≤ pairedEtaInverseRectangleBudget E D := by
  have hER : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hEDR : (1 : ℝ) ≤ (E * D : ℕ) := by exact_mod_cast (show 1 ≤ E * D by nlinarith)
  have hL : 1 ≤ (1 + Real.log E) ^ 2 := by nlinarith [Real.log_nonneg hER]
  have hT : 1 ≤ (1 + Real.log (E * D : ℕ)) ^ 2 := by nlinarith [Real.log_nonneg hEDR]
  have harea : (1 : ℝ) ≤ (E : ℝ) * D := by nlinarith
  have hfirst : (1 : ℝ) ≤ ((E : ℝ) * D) * (1 + Real.log E) ^ 2 := by nlinarith
  unfold pairedEtaInverseRectangleBudget
  nlinarith

/-- The mean square of the complete original rectangle with its common physical power. -/
def pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare
    (rho : NontrivialZetaZero) (k A L E D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖((A + n : ℕ) : ℂ) ^ rho.1 *
    pairedEtaCompletedMomentInverseRectangle rho k (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) E D‖ ^ 2) / L

/-- The mean square of the unmodified original inverse rectangle at its actual moving center. -/
def pairedEtaCompletedMomentInverseRectangleMeanSquare
    (rho : NontrivialZetaZero) (k A L E D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaCompletedMomentInverseRectangle rho k
    (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) E D‖ ^ 2) / L

/-- The full physical rectangle square is bounded only after retaining
its exact complex parity family and complete product-normalization error. -/
theorem pairedEtaCompletedMomentInverseRectangle_physical_sq_le
    (rho : NontrivialZetaZero) {k A M E D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hA : 1 ≤ A) (hAM : A ≤ M) (hED : E * D ≤ A) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRectangle rho k a M E D‖ ^ 2 ≤
      2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 * ‖pairedEtaInverseRectangleParityFamily M E D‖ ^ 2 +
        2 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * ((E : ℝ) * D) ^ 4 / (A : ℝ) ^ 2 := by
  let C := pairedEtaMomentDivisorAtomPhysicalConstant rho k
  have hC : 0 ≤ C := pairedEtaMomentDivisorAtomPhysicalConstant_nonneg rho k
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have he : ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRectangle rho k a M E D -
      pairedEtaMomentDivisorAmplitude rho k * pairedEtaInverseRectangleParityFamily M E D‖ ≤
        C * ((E : ℝ) * D) ^ 2 / A := by
    apply (norm_pairedEtaCompletedMomentInverseRectangle_physical_sub_parity_le rho hk
      (hED.trans hAM) ha).trans
    exact div_le_div_of_nonneg_left (by positivity) hAR (by exact_mod_cast hAM)
  have hz := (norm_le_insert'
    ((M : ℂ) ^ rho.1 * pairedEtaCompletedMomentInverseRectangle rho k a M E D)
    (pairedEtaMomentDivisorAmplitude rho k * pairedEtaInverseRectangleParityFamily M E D)).trans
      (add_le_add le_rfl he)
  rw [norm_mul (pairedEtaMomentDivisorAmplitude rho k)] at hz
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz
  have hh := sq_nonneg (‖pairedEtaMomentDivisorAmplitude rho k‖ *
    ‖pairedEtaInverseRectangleParityFamily M E D‖ - C * ((E : ℝ) * D) ^ 2 / A)
  calc
    _ ≤ 2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 * ‖pairedEtaInverseRectangleParityFamily M E D‖ ^ 2 +
        2 * (C * ((E : ℝ) * D) ^ 2 / A) ^ 2 := by nlinarith
    _ = _ := by dsimp [C]; ring

/-- Averaging keeps the complete rectangle phase energy and its
uniform physical correction as separate explicit terms. -/
theorem pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare_le_parity
    (rho : NontrivialZetaZero) {k A L E D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hA : 1 ≤ A) (hL : 0 < L) (hED : E * D ≤ A) :
    pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare rho k A L E D ≤
      2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
        ((∑ n ∈ Finset.range L, ‖pairedEtaInverseRectangleParityFamily (A + n) E D‖ ^ 2) / L) +
      2 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 * ((E : ℝ) * D) ^ 4 / (A : ℝ) ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  unfold pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare
  calc
    _ ≤ (∑ n ∈ Finset.range L,
        (2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 *
          ‖pairedEtaInverseRectangleParityFamily (A + n) E D‖ ^ 2 +
        2 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2 *
          ((E : ℝ) * D) ^ 4 / (A : ℝ) ^ 2)) / (L : ℝ) := by
      apply div_le_div_of_nonneg_right _ hLR.le
      apply Finset.sum_le_sum
      intro n hn
      have hM : (0 : ℝ) < (A + n : ℕ) := by exact_mod_cast (show 1 ≤ A + n by omega)
      exact pairedEtaCompletedMomentInverseRectangle_physical_sq_le rho hk hA (by omega) hED
        ⟨Real.log_le_log hM (by linarith), le_rfl⟩
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- The explicit completion and moment constant for joint control
of both divisor sums in the original inverse rectangle. -/
def pairedEtaCompletedMomentInverseRectangleConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  10 * finiteCircleSamplingConstant * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2 +
    2 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2

/-- The common-power inverse rectangle has area times logarithmic
mean square throughout the proved quadratic product range. -/
theorem pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) {k A L E D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hE : 1 ≤ E) (hD : 1 ≤ D) (hEDA : (E * D) ^ 2 ≤ A) (hEDL : (E * D) ^ 2 ≤ L) :
    pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare rho k A L E D ≤
      pairedEtaCompletedMomentInverseRectangleConstant rho k * pairedEtaInverseRectangleBudget E D := by
  have hED : 1 ≤ E * D := by nlinarith
  have hA : 1 ≤ A := (pow_pos hED 2).trans_le hEDA
  have hL : 0 < L := (pow_pos hED 2).trans_le hEDL
  have hEDle : E * D ≤ A := (Nat.le_self_pow (by decide : 2 ≠ 0) (E * D)).trans hEDA
  have hcost : ((E : ℝ) * D) ^ 4 / (A : ℝ) ^ 2 ≤ pairedEtaInverseRectangleBudget E D := by
    have h := (divisor_fourth_div_cutoff_sq_le_one hA hEDA).trans
      (one_le_pairedEtaInverseRectangleBudget hE hD)
    simpa only [Nat.cast_mul] using h
  have he := mul_le_mul_of_nonneg_left hcost
    (by positivity : 0 ≤ 2 * pairedEtaMomentDivisorAtomPhysicalConstant rho k ^ 2)
  have hp : (∑ n ∈ Finset.range L, ‖pairedEtaInverseRectangleParityFamily (A + n) E D‖ ^ 2) / L ≤
      5 * finiteCircleSamplingConstant * pairedEtaInverseRectangleBudget E D := by
    convert pairedEtaInverseRectangleParityFamily_meanSquare_le A hE hD hEDL using 1
    unfold pairedEtaInverseRectangleBudget
    ring
  have hm := mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ 2 * ‖pairedEtaMomentDivisorAmplitude rho k‖ ^ 2)
  apply (pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare_le_parity rho hk hA hL hEDle).trans
  simp only [← mul_div_assoc] at he
  unfold pairedEtaCompletedMomentInverseRectangleConstant
  nlinarith

/-- Removing the common physical power retains the actual zero's
horizontal decay for the complete original rectangle mean square. -/
theorem pairedEtaCompletedMomentInverseRectangleMeanSquare_le_physical
    (rho : NontrivialZetaZero) (k : ℕ) {A : ℕ} (hA : 1 ≤ A) (L E D : ℕ) :
    pairedEtaCompletedMomentInverseRectangleMeanSquare rho k A L E D ≤
      (A : ℝ) ^ (-2 * rho.1.re) *
        pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare rho k A L E D := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  unfold pairedEtaCompletedMomentInverseRectangleMeanSquare
    pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  apply Finset.sum_le_sum
  intro n hn
  rw [pairedEtaCompletedMomentInverseRectangle_norm_sq_eq_physical rho k _ (by omega)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos hAR (by exact_mod_cast (Nat.le_add_right A n))
    (by linarith [NontrivialZetaZero.zero_lt_re rho])

/-- Both actual inverse divisor sums have a joint physical mean-square
bound at the original moving center, below the full analytic multiplicity.
Every arithmetic, Fourier-support, and normalization premise is discharged. -/
theorem pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) {k A L E D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hE : 1 ≤ E) (hD : 1 ≤ D) (hEDA : (E * D) ^ 2 ≤ A) (hEDL : (E * D) ^ 2 ≤ L) :
    pairedEtaCompletedMomentInverseRectangleMeanSquare rho k A L E D ≤
      pairedEtaCompletedMomentInverseRectangleConstant rho k * pairedEtaInverseRectangleBudget E D *
        (A : ℝ) ^ (-2 * rho.1.re) := by
  have hED : 1 ≤ E * D := by nlinarith
  have hA : 1 ≤ A := (pow_pos hED 2).trans_le hEDA
  apply (pairedEtaCompletedMomentInverseRectangleMeanSquare_le_physical rho k hA L E D).trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMomentInverseRectanglePhysicalMeanSquare_le_quadratic rho hk hE hD hEDA hEDL)
    (Real.rpow_nonneg (Nat.cast_nonneg A) (-2 * rho.1.re))
  convert h using 1
  ring

end

end RiemannGaussian
