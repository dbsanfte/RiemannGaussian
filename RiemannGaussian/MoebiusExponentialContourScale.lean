import RiemannGaussian.MoebiusFiniteContourBound

/-!
# An exponentially growing contour and shrinking arithmetic heat

The actual reciprocal contour is evaluated at height `exp(h)` and heat
time `exp(-h)`. A cubic logarithmic arithmetic center makes the proved
left-line gain dominate the complete reciprocal envelope. The Gaussian
tail exponent controls every right-line correction on the same schedule.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The logarithmic arithmetic center used with the exponential contour and heat schedule. -/
def moebiusFiniteContourCenter (h : ℝ) : ℝ := 1000000000000000 * h ^ 3

/-- At the actual exponential height, the complete local logarithmic height is at most twice its scale parameter. -/
theorem localZetaLogHeight_exp_le {h : ℝ} (hh : 22 ≤ h) :
    localZetaLogHeight (Real.exp h) ≤ 2 * h := by
  have he := Real.add_one_le_exp h
  have hb : Real.exp h + 22 ≤ Real.exp (2 * h) := by
    rw [show 2 * h = h + h by ring, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp h - 1)]
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp h + 22) hb
  simpa only [localZetaLogHeight, abs_of_pos (Real.exp_pos h), Real.log_exp] using hlog

/-- The entire reciprocal contour norm is controlled quantitatively on the exponential height schedule. -/
theorem zetaReciprocalContourBound_exp_le {h : ℝ} (hh : 22 ≤ h) :
    zetaReciprocalContourBound (Real.exp h) ≤ gaussianMoebiusContourConstant * Real.exp (132000000 * h ^ 2) := by
  apply (zetaReciprocalContourBound_le_logSquare (Real.exp h)).trans
  have hL := localZetaLogHeight_exp_le hh
  have hpos := two_lt_localZetaLogHeight (Real.exp h)
  have hC : 0 ≤ gaussianMoebiusContourConstant := by linarith [sixteen_le_gaussianMoebiusContourConstant]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  nlinarith [sq_nonneg (2 * h - localZetaLogHeight (Real.exp h))]

/-- The actual cubic center extracts a quadratic gain from the proved reciprocal contour width. -/
theorem moebiusFiniteContourCenter_mul_width_ge {h : ℝ} (hh : 22 ≤ h)
    (hlarge : 1 / (500000 * zetaReciprocalLowHeightWidth) ≤ h) :
    1000000000 * h ^ 2 ≤ moebiusFiniteContourCenter h * zetaReciprocalContourWidth (Real.exp h) := by
  have hT : 2 ≤ Real.exp h := by linarith [Real.add_one_le_exp h]
  have hL := localZetaLogHeight_exp_le hh
  have hpos : 0 < localZetaLogHeight (Real.exp h) := by linarith [two_lt_localZetaLogHeight (Real.exp h)]
  rw [zetaReciprocalContourWidth_eq_stripWidth hT (Real.exp_le_exp.mpr hlarge),
    zetaReciprocalStripWidth, mul_one_div]
  rw [le_div_iff₀ (by positivity)]
  unfold moebiusFiniteContourCenter
  nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ 2 * h - localZetaLogHeight (Real.exp h) by linarith)]

/-- The actual moving absolute Möbius mass is linear in the exponential contour's logarithmic scale. -/
theorem moebiusDirichletMass_expContour_le {h : ℝ} (hh : 22 ≤ h)
    (hlarge : 1 / (500000 * zetaReciprocalLowHeightWidth) ≤ h) :
    moebiusDirichletMass (1 + zetaReciprocalContourWidth (Real.exp h)) ≤ 4000000 * h := by
  apply (moebiusDirichletMass_contour_le_log
    (show 2 ≤ Real.exp h by linarith [Real.add_one_le_exp h]) (Real.exp_le_exp.mpr hlarge)).trans
  linarith [localZetaLogHeight_exp_le hh]

/-- The complete tail suppression parameter is exact under the paired exponential height and heat schedule. -/
theorem moebius_exponentialHeat_mul_height_sq (h : ℝ) :
    Real.exp (-h) * Real.exp h ^ 2 = Real.exp h := by
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The Gaussian tail normalization retains its full height dependence on the shrinking heat schedule. -/
theorem moebius_exponentialHeat_tail_sqrt (h : ℝ) :
    Real.sqrt (2 * Real.pi / Real.exp (-h)) = Real.sqrt (2 * Real.pi) * Real.exp (h / 2) := by
  rw [Real.exp_neg, div_inv_eq_mul, Real.sqrt_mul (by positivity)]
  have hs := sqrt_exp_neg_moebiusHeatTime (-h)
  simpa only [neg_neg] using congrArg (fun x : ℝ ↦ Real.sqrt (2 * Real.pi) * x) hs

/-- All size conditions for the actual cubic center and exponential contour hold simultaneously beyond one fixed threshold. -/
theorem eventually_moebiusExponentialContour_conditions :
    ∀ᶠ h : ℝ in atTop, 22 ≤ h ∧
      1 / (500000 * zetaReciprocalLowHeightWidth) ≤ h ∧
      4 * moebiusFiniteContourCenter h ≤ Real.exp h := by
  have hexp := (Real.tendsto_exp_div_pow_atTop 3).eventually
    (eventually_ge_atTop (4000000000000000 : ℝ))
  filter_upwards [eventually_ge_atTop (22 : ℝ),
    eventually_ge_atTop (1 / (500000 * zetaReciprocalLowHeightWidth)), hexp] with h hh hl he
  refine ⟨hh, hl, ?_⟩
  have hpos : 0 < h ^ 3 := pow_pos (by linarith) _
  have hg := (le_div_iff₀ hpos).mp he
  dsimp [moebiusFiniteContourCenter]
  nlinarith

end

end RiemannGaussian
