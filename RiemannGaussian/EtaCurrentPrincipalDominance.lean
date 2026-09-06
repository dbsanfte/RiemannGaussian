import RiemannGaussian.EtaCurrentPrincipalEndpoints

/-!
# Dominance of the slower actual principal endpoint channel

The signed principal term factors into its slower positive horizontal
decay and an explicit difference of positive completion coefficients.
At a hypothetical off-critical zero the faster channel tends to zero
relative to the slower one. This gives an eventual lower bound, retaining
the actual coefficients and the original arithmetic cutoff.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The coefficient of the slower principal endpoint decay. -/
def pairedEtaCurrentDominantCoefficient (rho : NontrivialZetaZero) : ℝ :=
  if rho.1.re ≤ 1 / 2 then pairedEtaCurrentPrincipalCoefficient rho
  else pairedEtaCurrentPrincipalCoefficient (NontrivialZetaZero.conjugatePartner rho)

/-- The coefficient of the complementary faster principal endpoint decay. -/
def pairedEtaCurrentRecessiveCoefficient (rho : NontrivialZetaZero) : ℝ :=
  if rho.1.re ≤ 1 / 2 then pairedEtaCurrentPrincipalCoefficient (NontrivialZetaZero.conjugatePartner rho)
  else pairedEtaCurrentPrincipalCoefficient rho

/-- The dominant coefficient is strictly positive for every actual zero. -/
theorem pairedEtaCurrentDominantCoefficient_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaCurrentDominantCoefficient rho := by
  unfold pairedEtaCurrentDominantCoefficient
  split <;> exact pairedEtaCurrentPrincipalCoefficient_pos _

/-- The recessive coefficient is also strictly positive. -/
theorem pairedEtaCurrentRecessiveCoefficient_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaCurrentRecessiveCoefficient rho := by
  unfold pairedEtaCurrentRecessiveCoefficient
  split <;> exact pairedEtaCurrentPrincipalCoefficient_pos _

/-- The exact signed factorization retains which side of the critical
line supplies the slower completion channel before absolute values. -/
theorem pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentPrincipalEndpoint rho N =
      (if rho.1.re ≤ 1 / 2 then -1 else 1) *
        (pairedEtaLogTailShiftIncrement (N + 1) *
          Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) *
            (pairedEtaCurrentDominantCoefficient rho - pairedEtaCurrentRecessiveCoefficient rho *
              Real.exp (-2 * pairedEtaCurrentHorizontalDisplacement rho * pairedEtaLogTailCutoff (N + 2)))) := by
  rw [pairedEtaCurrentPrincipalEndpoint_eq_complementary]
  by_cases hs : rho.1.re ≤ 1 / 2
  · have he : pairedEtaCurrentHorizontalDisplacement rho = 1 - 2 * rho.1.re := by
      unfold pairedEtaCurrentHorizontalDisplacement
      rw [abs_of_nonpos (by linarith)]
      ring
    have hfast : Real.exp (-2 * (1 - rho.1.re) * pairedEtaLogTailCutoff (N + 2)) =
        Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) *
          Real.exp (-2 * pairedEtaCurrentHorizontalDisplacement rho * pairedEtaLogTailCutoff (N + 2)) := by
      rw [← Real.exp_add, he]
      congr 1
      ring
    have hslow : -2 * rho.1.re = pairedEtaCurrentHorizontalDisplacement rho - 1 := by rw [he]; ring
    rw [hfast, hslow]
    simp only [pairedEtaCurrentDominantCoefficient, pairedEtaCurrentRecessiveCoefficient, if_pos hs]
    ring
  · have he : pairedEtaCurrentHorizontalDisplacement rho = 2 * rho.1.re - 1 := by
      unfold pairedEtaCurrentHorizontalDisplacement
      rw [abs_of_nonneg (by linarith)]
    have hfast : Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2)) =
        Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) *
          Real.exp (-2 * pairedEtaCurrentHorizontalDisplacement rho * pairedEtaLogTailCutoff (N + 2)) := by
      rw [← Real.exp_add, he]
      congr 1
      ring
    have hslow : -2 * (1 - rho.1.re) = pairedEtaCurrentHorizontalDisplacement rho - 1 := by rw [he]; ring
    rw [hfast, hslow]
    simp only [pairedEtaCurrentDominantCoefficient, pairedEtaCurrentRecessiveCoefficient, if_neg hs]
    ring

/-- Taking the absolute value loses only the explicitly retained side
sign; the signed coefficient difference remains inside the absolute value. -/
theorem abs_pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCurrentPrincipalEndpoint rho N| =
      pairedEtaLogTailShiftIncrement (N + 1) *
        Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) *
          |pairedEtaCurrentDominantCoefficient rho - pairedEtaCurrentRecessiveCoefficient rho *
            Real.exp (-2 * pairedEtaCurrentHorizontalDisplacement rho * pairedEtaLogTailCutoff (N + 2))| := by
  rw [pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor, abs_mul]
  have hs : |(if rho.1.re ≤ 1 / 2 then -1 else 1 : ℝ)| = 1 := by split <;> norm_num
  rw [hs, one_mul, abs_mul, abs_mul,
    abs_of_pos (pairedEtaLogTailShiftIncrement_pos (N + 1)), abs_of_pos (Real.exp_pos _)]

/-- The actual successor logarithmic endpoints tend to infinity. -/
theorem tendsto_pairedEtaCurrent_successor_cutoff_atTop :
    Tendsto (fun N : ℕ ↦ pairedEtaLogTailCutoff (N + 2)) atTop atTop := by
  have h := Real.tendsto_log_atTop.comp
    (tendsto_atTop_add_const_right atTop 5
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  convert h using 1
  ext N
  unfold pairedEtaLogTailCutoff
  push_cast
  congr 1
  ring

/-- At an actual off-critical zero the faster completion channel tends
to zero relative to the slower one. -/
theorem tendsto_pairedEtaCurrent_relative_recessive_zero (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    Tendsto (fun N : ℕ ↦ pairedEtaCurrentRecessiveCoefficient rho *
      Real.exp (-2 * pairedEtaCurrentHorizontalDisplacement rho * pairedEtaLogTailCutoff (N + 2))) atTop (𝓝 0) := by
  have he := pairedEtaCurrentHorizontalDisplacement_pos rho hrho
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_pairedEtaCurrent_successor_cutoff_atTop.const_mul_atTop (by positivity : 0 < 2 * pairedEtaCurrentHorizontalDisplacement rho))
  simpa only [Function.comp_apply, neg_mul, mul_zero] using ht.const_mul (pairedEtaCurrentRecessiveCoefficient rho)

/-- Half the actual positive dominant coefficient survives eventually
at every hypothetical off-critical zero. -/
theorem pairedEtaCurrentPrincipalEndpoint_dominant_lower_eventually (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaLogTailShiftIncrement (N + 1) *
        Real.exp ((pairedEtaCurrentHorizontalDisplacement rho - 1) * pairedEtaLogTailCutoff (N + 2)) *
          (pairedEtaCurrentDominantCoefficient rho / 2) ≤ |pairedEtaCurrentPrincipalEndpoint rho N| := by
  have hA := pairedEtaCurrentDominantCoefficient_pos rho
  have hsmall := (tendsto_pairedEtaCurrent_relative_recessive_zero rho hrho).eventually_lt_const
    (by positivity : 0 < pairedEtaCurrentDominantCoefficient rho / 2)
  filter_upwards [hsmall] with N hN
  rw [abs_pairedEtaCurrentPrincipalEndpoint_eq_dominant_factor]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (pairedEtaLogTailShiftIncrement_pos (N + 1)).le (Real.exp_pos _).le)
  exact (show pairedEtaCurrentDominantCoefficient rho / 2 ≤ pairedEtaCurrentDominantCoefficient rho -
    pairedEtaCurrentRecessiveCoefficient rho *
      Real.exp (-2 * pairedEtaCurrentHorizontalDisplacement rho * pairedEtaLogTailCutoff (N + 2)) by linarith).trans
        (le_abs_self _)

end

end RiemannGaussian
