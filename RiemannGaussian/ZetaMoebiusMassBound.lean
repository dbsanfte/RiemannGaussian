import RiemannGaussian.GaussianMoebiusContourBound

/-!
# The moving Möbius mass from the actual eta bound

The absolute Möbius Dirichlet mass is bounded by the positive real zeta
series. The existing eta estimate then controls it by four divided by the
distance to one. This discharges the moving mass in the Gaussian contour
without assuming any Möbius cancellation.
-/

open Complex
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The absolute Möbius Dirichlet mass is bounded by the actual positive real zeta series. -/
theorem moebiusDirichletMass_le_norm_zeta {sigma : ℝ} (hsigma : 1 < sigma) :
    moebiusDirichletMass sigma ≤ ‖riemannZeta (sigma : ℂ)‖ := by
  let Z := ∑' n : ℕ, ((n : ℝ) ^ sigma)⁻¹
  have hZ : Summable (fun n : ℕ ↦ ((n : ℝ) ^ sigma)⁻¹) := Real.summable_nat_rpow_inv.mpr hsigma
  have hZpos : 0 ≤ Z := tsum_nonneg fun n ↦ by positivity
  have hZe : (Z : ℂ) = riemannZeta (sigma : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hsigma]
    dsimp [Z]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp only [one_div, Complex.ofReal_natCast]
  rw [← hZe, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hZpos]
  apply (summable_moebiusDirichletMass hsigma).tsum_le_tsum _ hZ
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero]
    positivity
  rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    Complex.ofReal_re, inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) sigma)
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- The original eta estimate bounds the actual moving Möbius mass near one. -/
theorem moebiusDirichletMass_one_add_le_four_div {w : ℝ} (hw : 0 < w) (hwle : w ≤ 1 / 2) :
    moebiusDirichletMass (1 + w) ≤ 4 / w := by
  exact (moebiusDirichletMass_le_norm_zeta (by linarith)).trans
    (by simpa using norm_riemannZeta_one_add_le_four_div hw hwle)

/-- The moving contour mass is controlled by its proved positive width at every height. -/
theorem moebiusDirichletMass_contour_le_four_div (T : ℝ) :
    moebiusDirichletMass (1 + zetaReciprocalContourWidth T) ≤ 4 / zetaReciprocalContourWidth T :=
  moebiusDirichletMass_one_add_le_four_div (zetaReciprocalContourWidth_pos T)
    (by linarith [zetaReciprocalContourWidth_le_eighth T])

/-- Once the compact middle no longer limits the width, the actual contour mass grows at most logarithmically. -/
theorem moebiusDirichletMass_contour_le_log {T : ℝ} (hT : 2 ≤ T)
    (hlarge : Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth)) ≤ T) :
    moebiusDirichletMass (1 + zetaReciprocalContourWidth T) ≤ 2000000 * localZetaLogHeight T := by
  apply (moebiusDirichletMass_contour_le_four_div T).trans_eq
  rw [zetaReciprocalContourWidth_eq_stripWidth hT hlarge, zetaReciprocalStripWidth]
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  ring

end

end RiemannGaussian
