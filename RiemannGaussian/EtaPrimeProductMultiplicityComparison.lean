import RiemannGaussian.EtaPrimeProductMultiplicityMargin

/-!
# Comparing the original and multiplicity-dependent zero margins

The explicit higher-order margin agrees with the previous margin at
multiplicity one and is strictly larger at every nonzero ordinate for
multiplicity at least two. This comparison is algebraic and is proved
before reporting a stronger zero-location or return-exponent bound.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The original rational-power margin lies below the smaller disc
threshold at every ordinate, so its old minimum is never active. -/
theorem etaPrimeProduct_zero_ratio_lt_sixteenth (y : ℝ) :
    |y| ^ 5 / (16 * 3200 ^ 3 * 64 ^ 4 * (|y| + 21) ^ 10) < 1 / 16 := by
  have hp : |y| ^ 5 ≤ (|y| + 21) ^ 10 :=
    (pow_le_pow_left₀ (abs_nonneg y) (by linarith : |y| ≤ |y| + 21) 5).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg y] : 1 ≤ |y| + 21) (by omega : 5 ≤ 10))
  have hden : 0 < 16 * 3200 ^ 3 * 64 ^ 4 * (|y| + 21) ^ 10 := by positivity
  calc
    _ ≤ (|y| + 21) ^ 10 / (16 * 3200 ^ 3 * 64 ^ 4 * (|y| + 21) ^ 10) :=
      div_le_div_of_nonneg_right hp hden.le
    _ = 1 / (16 * 3200 ^ 3 * 64 ^ 4) := by field_simp
    _ < _ := by norm_num

/-- The original margin equals its explicit ratio at every ordinate. -/
theorem etaPrimeProductZeroMargin_eq_ratio (y : ℝ) :
    etaPrimeProductZeroMargin y = |y| ^ 5 / (16 * 3200 ^ 3 * 64 ^ 4 * (|y| + 21) ^ 10) := by
  apply min_eq_right
  linarith [etaPrimeProduct_zero_ratio_lt_sixteenth y]

/-- The previous margin is strictly below the new disc threshold. -/
theorem etaPrimeProductZeroMargin_lt_sixteenth (y : ℝ) : etaPrimeProductZeroMargin y < 1 / 16 := by
  rw [etaPrimeProductZeroMargin_eq_ratio]
  exact etaPrimeProduct_zero_ratio_lt_sixteenth y

/-- At multiplicity one the higher-order formula reproduces the exact
previous margin, without weakening its constants or cutoff. -/
theorem etaPrimeProductMultiplicityZeroMargin_one (y : ℝ) :
    etaPrimeProductMultiplicityZeroMargin 1 y = etaPrimeProductZeroMargin y := by
  rw [etaPrimeProductZeroMargin_eq_ratio]
  norm_num only [etaPrimeProductMultiplicityZeroMargin, Nat.mul_one, Nat.reduceAdd, Nat.reduceSub,
    Nat.cast_one, inv_one, Real.rpow_one]
  apply min_eq_right
  have h := (etaPrimeProduct_zero_ratio_lt_sixteenth y).le
  norm_num at h
  exact h

/-- The higher-order prime-product ratio differs from the original
margin by an explicit dyadic power. -/
theorem etaPrimeProduct_multiplicity_ratio_eq (m : ℕ) (hm : 1 ≤ m) (y : ℝ) :
    |y| ^ 5 / (16 * 3200 ^ 3 * 8 ^ (4 * m + 4) * (|y| + 21) ^ 10) =
      etaPrimeProductZeroMargin y / 8 ^ (4 * m - 4) := by
  rw [etaPrimeProductZeroMargin_eq_ratio]
  have hp : (8 : ℝ) ^ (4 * m + 4) = 8 ^ 8 * 8 ^ (4 * m - 4) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  norm_num
  field_simp
  ring

/-- Every multiplicity at least two strictly improves the proved
zero margin at every nonzero ordinate. -/
theorem etaPrimeProductZeroMargin_lt_multiplicity (m : ℕ) (hm : 2 ≤ m)
    {y : ℝ} (hy : y ≠ 0) :
    etaPrimeProductZeroMargin y < etaPrimeProductMultiplicityZeroMargin m y := by
  have hb := etaPrimeProductZeroMargin_pos hy
  have hsmall := etaPrimeProductZeroMargin_lt_sixteenth y
  have hk : 0 < 4 * m - 4 := by omega
  have hp : 0 < 4 * m - 3 := by omega
  have hpR : 0 < ((4 * m - 3 : ℕ) : ℝ) := by exact_mod_cast hp
  have hpow : (8 * etaPrimeProductZeroMargin y) ^ (4 * m - 4) < 1 :=
    pow_lt_one₀ (by positivity) (by linarith) hk.ne'
  have hratio : etaPrimeProductZeroMargin y ^ (4 * m - 3) <
      etaPrimeProductZeroMargin y / 8 ^ (4 * m - 4) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 8 ^ (4 * m - 4))]
    have h := mul_lt_mul_of_pos_left hpow hb
    rw [mul_one, mul_pow] at h
    have he : 4 * m - 3 = (4 * m - 4) + 1 := by omega
    rw [he, pow_succ]
    convert h using 1
    ring
  have hroot := Real.rpow_lt_rpow (pow_nonneg hb.le _) hratio (inv_pos.mpr hpR)
  rw [Real.pow_rpow_inv_natCast hb.le hp.ne'] at hroot
  unfold etaPrimeProductMultiplicityZeroMargin
  rw [etaPrimeProduct_multiplicity_ratio_eq m (by omega) y]
  exact lt_min hsmall hroot

/-- The multiplicity margin never weakens the existing explicit zero
bound for any actual nontrivial zero. -/
theorem etaPrimeProductZeroMargin_le_actual_multiplicity (rho : NontrivialZetaZero) :
    etaPrimeProductZeroMargin rho.1.im ≤
      etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [hm, etaPrimeProductMultiplicityZeroMargin_one]
  · exact (etaPrimeProductZeroMargin_lt_multiplicity _
      (by have hp := analyticZetaZeroMultiplicity_positive rho; omega)
      (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)).le

/-- At a repeated actual zero the new return-growth exponent is
strictly smaller than the earlier ordinate-only exponent. -/
theorem etaPrimeProductMultiplicity_return_exponent_lt (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) :
    1 - 2 * etaPrimeProductMultiplicityZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im <
      1 - 2 * etaPrimeProductZeroMargin rho.1.im := by
  linarith [etaPrimeProductZeroMargin_lt_multiplicity _ hm (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)]

end

end RiemannGaussian
