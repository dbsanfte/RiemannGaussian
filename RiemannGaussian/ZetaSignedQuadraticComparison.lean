import RiemannGaussian.ZetaSignedQuadraticMargin
import RiemannGaussian.ZetaSignedMarginComparison

/-!
# Quantified improvement of the actual signed zero margin

The rational quadratic margin preserves the simple-zero estimate at every
multiplicity. It exceeds thirty-one times the previous signed logarithmic
margin at every nonzero ordinate. A single reciprocal-logarithm formula
also applies uniformly above height one. All comparisons are exact real
inequalities, independent of numerical experiments.
-/

open Complex Set
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The actual simple-zero multiplicity weight is exactly one. -/
theorem zetaSignedMultiplicityWeight_one : zetaSignedMultiplicityWeight 1 = 1 := by
  norm_num [zetaSignedMultiplicityWeight]

/-- Retaining any multiplicity never reduces the new simple-zero margin. -/
theorem zetaSignedQuadraticZeroMargin_one_le (m : ℕ) (y : ℝ) :
    zetaSignedQuadraticZeroMargin 1 y ≤ zetaSignedQuadraticZeroMargin m y := by
  have hq := one_le_zetaSignedMultiplicityWeight m
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  unfold zetaSignedQuadraticZeroMargin
  rw [zetaSignedMultiplicityWeight_one, one_mul, mul_one]
  apply min_le_min le_rfl
  rw [div_le_div_iff₀ (by positivity) (zetaSignedQuadraticZeroMargin_den_pos m y)]
  have h := mul_nonneg (by linarith : 0 ≤ zetaSignedMultiplicityWeight m - 1)
    (show 0 ≤ 56448 * localZetaLogHeight y * |y| ^ 2 by positivity)
  nlinarith

/-- The new simple-zero formula exceeds thirty-one times the previous signed margin at every nonzero height. -/
theorem thirtyOne_mul_signedLogZeroMargin_lt_quadratic_one {y : ℝ} (hy : y ≠ 0) :
    31 * zetaSignedLogZeroMargin y < zetaSignedQuadraticZeroMargin 1 y := by
  have ht := abs_pos.mpr hy
  have hL := two_lt_localZetaLogHeight y
  have hLp : 0 < localZetaLogHeight y := by linarith
  unfold zetaSignedQuadraticZeroMargin
  rw [zetaSignedMultiplicityWeight_one, one_mul, mul_one]
  apply lt_min
  · linarith [zetaSignedLogZeroMargin_le_pole_width y]
  · have hden : 31 * (56448 * localZetaLogHeight y * |y| + 19) <
        1800000 * (|y| + 1) * localZetaLogHeight y := by
      nlinarith [mul_nonneg ht.le hLp.le]
    unfold zetaSignedLogZeroMargin
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
    calc
      _ = |y| * (31 * (56448 * localZetaLogHeight y * |y| + 19)) := by ring
      _ < |y| * (1800000 * (|y| + 1) * localZetaLogHeight y) := mul_lt_mul_of_pos_left hden ht

/-- The factor-thirty-one strict improvement holds with every actual multiplicity retained. -/
theorem thirtyOne_mul_signedLogZeroMargin_lt_quadratic (m : ℕ) {y : ℝ} (hy : y ≠ 0) :
    31 * zetaSignedLogZeroMargin y < zetaSignedQuadraticZeroMargin m y :=
  (thirtyOne_mul_signedLogZeroMargin_lt_quadratic_one hy).trans_le (zetaSignedQuadraticZeroMargin_one_le m y)

/-- Above height one, the improved margin has an explicit reciprocal-logarithm lower bound. -/
theorem one_div_logHeight_le_zetaSignedQuadraticZeroMargin (m : ℕ) {y : ℝ} (hy : 1 ≤ |y|) :
    1 / (56458 * localZetaLogHeight y) ≤ zetaSignedQuadraticZeroMargin m y := by
  apply le_trans _ (zetaSignedQuadraticZeroMargin_one_le m y)
  have hL := two_lt_localZetaLogHeight y
  have hLp : 0 < localZetaLogHeight y := by linarith
  unfold zetaSignedQuadraticZeroMargin
  rw [zetaSignedMultiplicityWeight_one, one_mul, mul_one]
  apply le_min
  · rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 24)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ |y| - 1) hLp.le]

/-- Every actual zero above height one lies in the improved literal reciprocal-logarithm strip. -/
theorem nontrivialZetaZero_mem_quadratic_reciprocal_log_strip (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Icc (1 / (56458 * localZetaLogHeight rho.1.im))
      (1 - 1 / (56458 * localZetaLogHeight rho.1.im)) := by
  have hz := nontrivialZetaZero_mem_signedQuadratic_strip rho
  have hmargin := one_div_logHeight_le_zetaSignedQuadraticZeroMargin (analyticZetaZeroMultiplicity rho) hy
  constructor <;> linarith [hz.1, hz.2]

end

end RiemannGaussian
