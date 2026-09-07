import RiemannGaussian.ZetaMoebiusMassBound

/-!
# Fixed constants for the actual Gaussian Möbius scale choice

The complete reciprocal envelope has at most a fixed constant times the
exponential of a squared logarithm. The fixed constant includes the proved
compact norm floor. No height-dependent factor is hidden in it.
-/

namespace RiemannGaussian

noncomputable section

/-- A fixed positive constant covering the actual compact reciprocal bound and high-height prefactor. -/
def gaussianMoebiusContourConstant : ℝ := max (6 / zetaReciprocalLowHeightFloor) 16

/-- The fixed contour constant is at least sixteen. -/
theorem sixteen_le_gaussianMoebiusContourConstant : 16 ≤ gaussianMoebiusContourConstant := le_max_right _ _

/-- The complete reciprocal envelope grows at most exponentially in a squared logarithm. -/
theorem zetaReciprocalContourBound_le_logSquare (T : ℝ) :
    zetaReciprocalContourBound T ≤ gaussianMoebiusContourConstant *
      Real.exp (33000000 * localZetaLogHeight T ^ 2) := by
  let L := localZetaLogHeight T
  have hL : 2 < L := two_lt_localZetaLogHeight T
  have hlog : Real.log (1000000 * L) ≤ 1000000 * L :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hcost : L + (40 * L + 32 * L * Real.log (1000000 * L)) ≤ 33000000 * L ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 32 * L by positivity)
    nlinarith [sq_nonneg (L - 2)]
  have hexp : 1 ≤ Real.exp (33000000 * L ^ 2) := Real.one_le_exp (by positivity)
  have hC : 0 ≤ gaussianMoebiusContourConstant := by linarith [sixteen_le_gaussianMoebiusContourConstant]
  apply max_le
  · exact (le_max_left _ _).trans (le_mul_of_one_le_right hC hexp)
  · unfold zetaReciprocalHeightBound
    have ht : |T| + 1 ≤ Real.exp L := by
      rw [show Real.exp L = |T| + 22 by exact Real.exp_log (by positivity)]
      linarith
    calc
      _ ≤ 16 * Real.exp L * Real.exp (40 * L + 32 * L * Real.log (1000000 * L)) := by gcongr
      _ = 16 * Real.exp (L + (40 * L + 32 * L * Real.log (1000000 * L))) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ gaussianMoebiusContourConstant * Real.exp (33000000 * L ^ 2) :=
        mul_le_mul sixteen_le_gaussianMoebiusContourConstant (Real.exp_le_exp.mpr hcost) (Real.exp_pos _).le hC

/-- A fixed prefactor including all three contour contributions at unit heat time. -/
def gaussianMoebiusScalePrefactor : ℝ :=
  gaussianMoebiusContourConstant * (3 + 4000000 * Real.sqrt (2 * Real.pi)) * Real.exp 2

/-- The scale prefactor is strictly positive. -/
theorem gaussianMoebiusScalePrefactor_pos : 0 < gaussianMoebiusScalePrefactor := by
  have hC : 0 < gaussianMoebiusContourConstant := by linarith [sixteen_le_gaussianMoebiusContourConstant]
  unfold gaussianMoebiusScalePrefactor
  positivity

/-- A fixed squared-logarithm exponent absorbing the complete scale prefactor. -/
def gaussianMoebiusScaleExponent : ℝ := 33000001 + |Real.log gaussianMoebiusScalePrefactor|

/-- The fixed exponent is strictly positive. -/
theorem gaussianMoebiusScaleExponent_pos : 0 < gaussianMoebiusScaleExponent := by
  unfold gaussianMoebiusScaleExponent
  positivity

end

end RiemannGaussian
