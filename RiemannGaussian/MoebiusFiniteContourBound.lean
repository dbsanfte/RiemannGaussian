import RiemannGaussian.GaussianMoebiusCumulativeBound
import RiemannGaussian.MoebiusFiniteCancellation

/-!
# A quantitative contour bound at an ordinary finite Möbius cutoff

The logarithmic Gaussian cutoff has normalized error at most nine times
the square root of its heat time. Combining this with the full cumulative
contour estimate bounds the literal unsmoothed finite prefix, including
integer rounding, negative centers, and every contour correction.
-/

open MeasureTheory

namespace RiemannGaussian

noncomputable section

/-- At heat time at most one quarter, the complete normalized Gaussian cutoff error has an explicit square-root rate. -/
theorem integral_moebiusCutoffGaussian_error_div_le_sqrt {tau : ℝ}
    (htau : 0 < tau) (htaule : tau ≤ 1 / 4) :
    (∫ v : ℝ, moebiusCutoffGaussian tau v * |Real.exp v - 1|) /
      moebiusCutoffGaussianMass tau ≤ 9 * Real.sqrt tau := by
  have he := Real.abs_exp_sub_one_le (show |4 * tau| ≤ 1 by
    rw [abs_of_nonneg (by positivity)]
    linarith)
  have hsq : Real.exp (4 * tau) - 2 * Real.exp tau + 1 ≤ 8 * tau := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 4 * tau)] at he
    have hp := Real.one_le_exp htau.le
    have ha := le_abs_self (Real.exp (4 * tau) - 1)
    linarith
  have hs := Real.sqrt_pos.mpr htau
  have h := integral_moebiusCutoffGaussian_abs_exp_sub_one_le htau hs
  have hd : (Real.exp (4 * tau) - 2 * Real.exp tau + 1) / Real.sqrt tau ≤ 8 * Real.sqrt tau := by
    rw [div_le_iff₀ hs]
    nlinarith [Real.sq_sqrt htau.le]
  have hdiv : (∫ v : ℝ, moebiusCutoffGaussian tau v * |Real.exp v - 1|) /
      moebiusCutoffGaussianMass tau ≤
        Real.sqrt tau + (Real.exp (4 * tau) - 2 * Real.exp tau + 1) / Real.sqrt tau :=
    (div_le_iff₀ (moebiusCutoffGaussianMass_pos htau)).mpr (by simpa only [mul_comm] using h)
  apply hdiv.trans
  linarith

/-- The literal ordinary finite prefix has a complete all-parameter contour estimate with a quantitative cutoff error. -/
theorem abs_moebiusLogPrefix_exp_ratio_le_contour {a tau T : ℝ}
    (ha : 0 ≤ a) (htau : 0 < tau) (htaule : tau ≤ 1 / 4) (hT : 2 ≤ T) :
    |moebiusLogPrefix a / Real.exp a| ≤
      9 * Real.sqrt tau + Real.exp (-a) +
        (moebiusDirichletMass 2 * Real.exp (4 * tau) / 2 +
          2 * gaussianMoebiusContourMajorant a tau T) /
            (Real.exp a * moebiusCutoffGaussianMass tau) := by
  have h := abs_moebiusLogPrefix_exp_ratio_le htau a
  have hU := abs_gaussianMoebiusCumulative_le_contourMajorant ha htau hT
  have hbound : |gaussianMoebiusCumulative a tau / Real.exp a| / moebiusCutoffGaussianMass tau ≤
      (moebiusDirichletMass 2 * Real.exp (4 * tau) / 2 + 2 * gaussianMoebiusContourMajorant a tau T) /
        (Real.exp a * moebiusCutoffGaussianMass tau) := by
    rw [abs_div, abs_of_pos (Real.exp_pos a), div_div]
    exact div_le_div_of_nonneg_right hU (by positivity [moebiusCutoffGaussianMass_pos htau])
  exact h.trans (add_le_add (add_le_add
    (integral_moebiusCutoffGaussian_error_div_le_sqrt htau htaule) le_rfl) hbound)

/-- The two Gaussian normalizations cancel exactly before estimating any contour contribution. -/
theorem moebiusCutoffGaussianMass_mul_reciprocalNormalization {tau : ℝ} (htau : 0 < tau) :
    moebiusCutoffGaussianMass tau * Real.sqrt (Real.pi / tau) = 2 * Real.pi := by
  unfold moebiusCutoffGaussianMass
  rw [← Real.sqrt_mul (by positivity)]
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  field_simp
  ring

/-- Exponential heat schedules retain the exact square-root time scale. -/
theorem sqrt_exp_neg_moebiusHeatTime (h : ℝ) : Real.sqrt (Real.exp (-h)) = Real.exp (-h / 2) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The finite-cutoff Gaussian mass is exact on the exponentially shrinking heat schedule. -/
theorem moebiusCutoffGaussianMass_exp_neg (h : ℝ) :
    moebiusCutoffGaussianMass (Real.exp (-h)) = Real.sqrt (4 * Real.pi) * Real.exp (-h / 2) := by
  unfold moebiusCutoffGaussianMass
  rw [Real.sqrt_mul (by positivity), sqrt_exp_neg_moebiusHeatTime]

end

end RiemannGaussian
