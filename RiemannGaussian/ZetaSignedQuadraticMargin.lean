import RiemannGaussian.ZetaSignedExactPole

/-!
# A stronger multiplicity-sensitive zero margin from the exact pole

The quadratic prime constraint is solved by an explicit positive rational
subsolution. Reflection supplies both boundaries of a literal zero-free
strip. The multiplicity weight remains positive even in the definition's
unused order-zero case; every actual zero uses its genuine positive order.
-/

open Complex Set
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- A positive rational subsolution converts the quadratic signed gap constraint into a boundary margin. -/
theorem rational_margin_le_of_quadratic_gap {A t q d : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hq : 1 ≤ q) (hd : 0 ≤ d) (hgap : q ≤ A * d + 357 * d ^ 2 / t ^ 2) :
    q * t / (A * t + 19 * q) ≤ d := by
  let r : ℝ := q * t / (A * t + 19 * q)
  have hqpos : 0 < q := by linarith
  have hden : 0 < A * t + 19 * q := by positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have he : A * r + 357 * r ^ 2 / t ^ 2 =
      (A * q * t * (A * t + 19 * q) + 357 * q ^ 2) / (A * t + 19 * q) ^ 2 := by
    dsimp [r]
    field_simp
  have htest : A * r + 357 * r ^ 2 / t ^ 2 < q := by
    rw [he]
    apply (div_lt_iff₀ (sq_pos_of_pos hden)).mpr
    have hp : 0 < (19 * A * t + 361 * q - 357) * q ^ 2 := by
      exact mul_pos (by nlinarith [mul_nonneg hA ht.le]) (sq_pos_of_pos hqpos)
    nlinarith
  by_contra h
  have hdr : d ≤ r := (lt_of_not_ge h).le
  have hs : d ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hd hr.le).mpr hdr
  have hmono : A * d + 357 * d ^ 2 / t ^ 2 ≤ A * r + 357 * r ^ 2 / t ^ 2 :=
    add_le_add (mul_le_mul_of_nonneg_left hdr hA)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (sq_nonneg t))
  exact (not_lt_of_ge (hgap.trans hmono)) htest

/-- The positive weight equals eight times the actual multiplicity minus seven. -/
def zetaSignedMultiplicityWeight (m : ℕ) : ℝ := 8 * ((m - 1 : ℕ) : ℝ) + 1

/-- Every defined multiplicity weight is at least one. -/
theorem one_le_zetaSignedMultiplicityWeight (m : ℕ) : 1 ≤ zetaSignedMultiplicityWeight m := by
  unfold zetaSignedMultiplicityWeight
  linarith [Nat.cast_nonneg (α := ℝ) (m - 1)]

/-- At each positive analytic order the weight retains the exact coefficient from the prime inequality. -/
theorem zetaSignedMultiplicityWeight_eq {m : ℕ} (hm : 1 ≤ m) :
    zetaSignedMultiplicityWeight m = 8 * (m : ℝ) - 7 := by
  simp only [zetaSignedMultiplicityWeight, Nat.cast_sub hm, Nat.cast_one]
  ring

/-- The explicit margin obtained from the shift-sensitive pole estimate and the complete multiplicity. -/
def zetaSignedQuadraticZeroMargin (m : ℕ) (y : ℝ) : ℝ :=
  min (1 / 24) (zetaSignedMultiplicityWeight m * |y| /
    (56448 * localZetaLogHeight y * |y| + 19 * zetaSignedMultiplicityWeight m))

/-- The rational margin has a strictly positive denominator at every ordinate. -/
theorem zetaSignedQuadraticZeroMargin_den_pos (m : ℕ) (y : ℝ) :
    0 < 56448 * localZetaLogHeight y * |y| + 19 * zetaSignedMultiplicityWeight m := by
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  have hq : 0 < zetaSignedMultiplicityWeight m := by linarith [one_le_zetaSignedMultiplicityWeight m]
  positivity

/-- The new explicit margin is positive at every actual nonzero ordinate. -/
theorem zetaSignedQuadraticZeroMargin_pos (m : ℕ) {y : ℝ} (hy : y ≠ 0) :
    0 < zetaSignedQuadraticZeroMargin m y := by
  have hq : 0 < zetaSignedMultiplicityWeight m := by linarith [one_le_zetaSignedMultiplicityWeight m]
  exact lt_min (by norm_num) (div_pos (mul_pos hq (abs_pos.mpr hy))
    (zetaSignedQuadraticZeroMargin_den_pos m y))

/-- The explicit cap handles zeros outside the local right-boundary neighborhood. -/
theorem zetaSignedQuadraticZeroMargin_le_one_div (m : ℕ) (y : ℝ) :
    zetaSignedQuadraticZeroMargin m y ≤ 1 / 24 := min_le_left _ _

/-- The new arithmetic margin applies to every original nontrivial zero, with its actual multiplicity. -/
theorem zetaSignedQuadraticZeroMargin_le_one_sub_re (rho : NontrivialZetaZero) :
    zetaSignedQuadraticZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ 1 - rho.1.re := by
  by_cases hrho : 23 / 24 ≤ rho.1.re
  · have hg := multiplicity_le_quadratic_signed_zero_gap rho hrho
    have hm := analyticZetaZeroMultiplicity_positive rho
    rw [← zetaSignedMultiplicityWeight_eq hm] at hg
    have hL : 0 < localZetaLogHeight rho.1.im := by linarith [two_lt_localZetaLogHeight rho.1.im]
    have hgap : zetaSignedMultiplicityWeight (analyticZetaZeroMultiplicity rho) ≤
        (56448 * localZetaLogHeight rho.1.im) * (1 - rho.1.re) +
          357 * (1 - rho.1.re) ^ 2 / |rho.1.im| ^ 2 := by simpa only [sq_abs] using hg
    exact (min_le_right _ _).trans (rational_margin_le_of_quadratic_gap (by positivity)
      (abs_pos.mpr (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)) (one_le_zetaSignedMultiplicityWeight _)
      (sub_nonneg.mpr (NontrivialZetaZero.re_lt_one rho).le) hgap)
  · exact (zetaSignedQuadraticZeroMargin_le_one_div _ _).trans (by linarith)

/-- Completion reflection gives the same multiplicity-sensitive left margin at the identical ordinate. -/
theorem zetaSignedQuadraticZeroMargin_le_re (rho : NontrivialZetaZero) :
    zetaSignedQuadraticZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ rho.1.re := by
  have h := zetaSignedQuadraticZeroMargin_le_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa only [analyticZetaZeroMultiplicity_conjugatePartner, NontrivialZetaZero.conjugatePartner_coe,
    Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- Every literal nontrivial zeta zero lies in the stronger explicitly specified strip. -/
theorem nontrivialZetaZero_mem_signedQuadratic_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc (zetaSignedQuadraticZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im)
      (1 - zetaSignedQuadraticZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) :=
  ⟨zetaSignedQuadraticZeroMargin_le_re rho, by linarith [zetaSignedQuadraticZeroMargin_le_one_sub_re rho]⟩

end

end RiemannGaussian
