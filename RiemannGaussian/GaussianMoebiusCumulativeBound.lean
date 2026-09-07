import RiemannGaussian.GaussianMoebiusPrimitive

/-!
# Quantitative cumulative Gaussian Möbius bounds

The full contour majorant is integrable in the arithmetic center up to
every finite cutoff. Its three contributions retain the left-line gain,
both horizontal corrections, and both infinite tails. The negative-center
part of the actual cumulative source has a separate Dirichlet bound.
No fixed-time limit or unquantified cancellation remainder is used here.
-/

open MeasureTheory Set

namespace RiemannGaussian

noncomputable section

/-- The complete actual Gaussian contour majorant, separated into its three center exponentials. -/
def gaussianMoebiusContourMajorant (a tau T : ℝ) : ℝ :=
  let w := zetaReciprocalContourWidth T
  let B := zetaReciprocalContourBound T
  let Q := Real.sqrt (Real.pi / tau)
  (2 * T * B * Real.exp (tau * (1 - w) ^ 2) / Q) * Real.exp ((1 - w) * a) +
    (4 * w * B * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2) / Q) * Real.exp ((1 + w) * a) +
    (moebiusDirichletMass (1 + w) * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2 / 2) *
      Real.sqrt (2 * Real.pi / tau) / Q) * Real.exp ((1 + w) * a)

/-- Every contribution to the full contour majorant is nonnegative at positive heat time and height. -/
theorem gaussianMoebiusContourMajorant_nonneg (a : ℝ) {tau T : ℝ}
    (htau : 0 < tau) (hT : 0 ≤ T) : 0 ≤ gaussianMoebiusContourMajorant a tau T := by
  have hw := zetaReciprocalContourWidth_pos T
  have hB := zetaReciprocalContourBound_pos T
  have hD := one_le_moebiusDirichletMass (show 1 < 1 + zetaReciprocalContourWidth T by linarith)
  unfold gaussianMoebiusContourMajorant
  positivity

/-- The separated majorant is exactly the proved three-term contour estimate on the actual source. -/
theorem abs_gaussianMoebiusSum_le_contourMajorant {a tau T : ℝ}
    (ha : 0 ≤ a) (htau : 0 < tau) (hT : 2 ≤ T) :
    |gaussianMoebiusSum a tau| ≤ gaussianMoebiusContourMajorant a tau T := by
  apply (gaussianMoebiusSum_contour_bound ha htau hT).trans_eq
  unfold gaussianMoebiusContourMajorant
  simp only [sub_eq_add_neg, Real.exp_add]
  ring_nf

/-- All three actual contour exponentials are integrable over the whole one-sided center range. -/
theorem integrableOn_gaussianMoebiusContourMajorant (a tau T : ℝ) :
    IntegrableOn (fun u : ℝ ↦ gaussianMoebiusContourMajorant u tau T) (Iic a) := by
  have hw := zetaReciprocalContourWidth_pos T
  have hwle := zetaReciprocalContourWidth_le_eighth T
  have hl := integrableOn_exp_mul_Iic (show 0 < 1 - zetaReciprocalContourWidth T by linarith) a
  have hr := integrableOn_exp_mul_Iic (show 0 < 1 + zetaReciprocalContourWidth T by linarith) a
  exact ((hl.const_mul _).add (hr.const_mul _)).add (hr.const_mul _)

/-- Integrating the complete contour envelope costs at most a factor two because both real slopes stay above one half. -/
theorem integral_gaussianMoebiusContourMajorant_le (a : ℝ) {tau T : ℝ}
    (htau : 0 < tau) (hT : 0 ≤ T) :
    (∫ u : ℝ in Iic a, gaussianMoebiusContourMajorant u tau T) ≤
      2 * gaussianMoebiusContourMajorant a tau T := by
  let w := zetaReciprocalContourWidth T
  have hw : 0 < w := zetaReciprocalContourWidth_pos T
  have hwle : w ≤ 1 / 8 := zetaReciprocalContourWidth_le_eighth T
  have hB := zetaReciprocalContourBound_pos T
  have hD := one_le_moebiusDirichletMass (show 1 < 1 + w by linarith)
  have hl := integrableOn_exp_mul_Iic (show 0 < 1 - w by linarith) a
  have hr := integrableOn_exp_mul_Iic (show 0 < 1 + w by linarith) a
  have hleft : Real.exp ((1 - w) * a) / (1 - w) ≤ 2 * Real.exp ((1 - w) * a) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - w)]
    nlinarith [Real.exp_pos ((1 - w) * a)]
  have hright : Real.exp ((1 + w) * a) / (1 + w) ≤ 2 * Real.exp ((1 + w) * a) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + w)]
    nlinarith [Real.exp_pos ((1 + w) * a)]
  let L := 2 * T * zetaReciprocalContourBound T * Real.exp (tau * (1 - w) ^ 2) /
    Real.sqrt (Real.pi / tau)
  let R := 4 * w * zetaReciprocalContourBound T * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2) /
    Real.sqrt (Real.pi / tau)
  let U := moebiusDirichletMass (1 + w) * Real.exp (tau * (1 + w) ^ 2 - tau * T ^ 2 / 2) *
    Real.sqrt (2 * Real.pi / tau) / Real.sqrt (Real.pi / tau)
  have hiLR : IntegrableOn (fun u : ℝ ↦ L * Real.exp ((1 - w) * u) +
      R * Real.exp ((1 + w) * u)) (Iic a) := (hl.const_mul L).add (hr.const_mul R)
  change (∫ u : ℝ in Iic a, (L * Real.exp ((1 - w) * u) + R * Real.exp ((1 + w) * u)) +
    U * Real.exp ((1 + w) * u)) ≤
      2 * ((L * Real.exp ((1 - w) * a) + R * Real.exp ((1 + w) * a)) + U * Real.exp ((1 + w) * a))
  rw [integral_add hiLR (hr.const_mul U), integral_add (hl.const_mul L) (hr.const_mul R)]
  simp only [integral_const_mul, integral_exp_mul_Iic (show 0 < 1 - w by linarith),
    integral_exp_mul_Iic (show 0 < 1 + w by linarith)]
  calc
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hleft (by positivity))
      (mul_le_mul_of_nonneg_left hright (by positivity)))
      (mul_le_mul_of_nonneg_left hright (by positivity))
    _ = _ := by ring

/-- The entire negative-center cumulative source has an explicit Dirichlet mass bound. -/
theorem abs_gaussianMoebiusCumulative_zero_le {tau : ℝ} (htau : 0 < tau) :
    |gaussianMoebiusCumulative 0 tau| ≤ moebiusDirichletMass 2 * Real.exp (4 * tau) / 2 := by
  have hg : IntegrableOn (fun u : ℝ ↦ (moebiusDirichletMass 2 * Real.exp (4 * tau)) *
      Real.exp (2 * u)) (Iic 0) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) 0).const_mul _
  have h := norm_integral_le_of_norm_le (f := fun u : ℝ ↦ gaussianMoebiusSum u tau) hg
    (Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]
      apply (abs_gaussianMoebiusSum_le_dirichlet u htau (by norm_num : (1 : ℝ) < 2)).trans_eq
      rw [show u * 2 + tau * (2 : ℝ) ^ 2 = 4 * tau + 2 * u by ring, Real.exp_add]
      ring)
  rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 2)] at h
  simpa only [mul_zero, Real.exp_zero, one_div, Real.norm_eq_abs, gaussianMoebiusCumulative,
    div_eq_mul_inv, one_mul] using h

/-- The complete cumulative signed source has a quantitative contour bound, with its negative-center contribution included. -/
theorem abs_gaussianMoebiusCumulative_le_contourMajorant {a tau T : ℝ}
    (ha : 0 ≤ a) (htau : 0 < tau) (hT : 2 ≤ T) :
    |gaussianMoebiusCumulative a tau| ≤
      moebiusDirichletMass 2 * Real.exp (4 * tau) / 2 + 2 * gaussianMoebiusContourMajorant a tau T := by
  have he : gaussianMoebiusCumulative a tau = gaussianMoebiusCumulative 0 tau +
      ∫ u : ℝ in Ioc 0 a, gaussianMoebiusSum u tau := by
    have h := intervalIntegral.integral_Iic_sub_Iic
      (integrableOn_gaussianMoebiusSum_Iic htau 0) (integrableOn_gaussianMoebiusSum_Iic htau a)
    rw [intervalIntegral.integral_of_le ha] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hm := integrableOn_gaussianMoebiusContourMajorant a tau T
  have hb : |∫ u : ℝ in Ioc 0 a, gaussianMoebiusSum u tau| ≤
      ∫ u : ℝ in Ioc 0 a, gaussianMoebiusContourMajorant u tau T := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (f := fun u : ℝ ↦ gaussianMoebiusSum u tau)
      (hm.mono_set (show Ioc 0 a ⊆ Iic a from fun _ h ↦ h.2))
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall fun u hu ↦ by
      rw [Real.norm_eq_abs]
      exact abs_gaussianMoebiusSum_le_contourMajorant hu.1.le htau hT
  have hset : (∫ u : ℝ in Ioc 0 a, gaussianMoebiusContourMajorant u tau T) ≤
      ∫ u : ℝ in Iic a, gaussianMoebiusContourMajorant u tau T :=
    setIntegral_mono_set hm
      (Filter.Eventually.of_forall fun u ↦ gaussianMoebiusContourMajorant_nonneg u htau (by linarith))
      (Filter.Eventually.of_forall fun _ h ↦ h.2)
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_gaussianMoebiusCumulative_zero_le htau)
    (hb.trans (hset.trans (integral_gaussianMoebiusContourMajorant_le a htau (by linarith)))))

end

end RiemannGaussian
