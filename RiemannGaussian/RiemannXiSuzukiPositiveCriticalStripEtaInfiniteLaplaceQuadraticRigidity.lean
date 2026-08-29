import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceRigidity

/-!
# Quadratic rigidity from the infinite eta measure

The first direct eta-measure zero constraint used the Lipschitz bound on
`1 - cos`.  This module retains one more order of the oscillation.  The global
quadratic estimate

`1 - cos u <= u^2 / 2`

combines with exact cosine cancellation and the complete second exponential
moment.  For every nontrivial zeta zero `rho`, Lean obtains

`rho.re * sqrt (1 - exp (-rho.re * log 2)) <= |rho.im|`,

or equivalently the squared inequality

`rho.re^2 * (1 - exp (-rho.re * log 2)) <= rho.im^2`.

The quadratic threshold is proved strictly larger than the earlier linear
threshold throughout the positive half-plane.  This is still a weak vertical
zero-exclusion estimate, not horizontal rigidity or a proof of RH.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The second exponentially tilted Lebesgue moment is integrable on the
positive half-line. -/
theorem integrableOn_sq_mul_exp_neg_mul_Ioi_zero
    {sigma : ℝ} (hsigma : 0 < sigma) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-sigma * t)) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun t : ℝ => t ^ 2 * Real.exp (-t)) (Ioi 0) := by
    have hgamma :=
      Real.GammaIntegral_convergent (s := (3 : ℝ)) (by norm_num)
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    norm_num [Real.rpow_two, mul_comm]
  have hscaled : IntegrableOn
      (fun t : ℝ => (sigma * t) ^ 2 * Real.exp (-(sigma * t)))
      (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => u ^ 2 * Real.exp (-u)) 0 hsigma).2 (by
        simpa using hbase)
  have hconst := hscaled.const_mul (sigma ^ 2)⁻¹
  apply hconst.congr
  filter_upwards with t
  field_simp [hsigma.ne']

/-- The complete second exponential moment on the positive half-line has its
elementary exact value. -/
theorem integral_sq_mul_exp_neg_mul_Ioi_zero
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-sigma * t)) =
      2 * sigma⁻¹ ^ 3 := by
  calc
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-sigma * t)) =
        ∫ t : ℝ in Ioi 0,
          t ^ ((3 : ℝ) - 1) * Real.exp (-(sigma * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      norm_num [Real.rpow_two]
    _ = 2 * sigma⁻¹ ^ 3 := by
      simpa [one_div, Real.rpow_two, mul_comm] using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi
          (a := (3 : ℝ)) (r := sigma) (by norm_num) hsigma)

/-- The second tilted moment of the fixed eta measure is integrable. -/
theorem integrable_sq_mul_exp_neg_mul_pairedEtaLogMeasure
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-sigma * t))
      pairedEtaLogMeasure := by
  exact Integrable.mono_measure
    (μ := pairedEtaLogMeasure) (ν := volume.restrict (Ioi 0))
    (integrableOn_sq_mul_exp_neg_mul_Ioi_zero hsigma)
    pairedEtaLogMeasure_le_volume_restrict_Ioi_zero

/-- The second tilted moment of the fixed eta measure is bounded by the
complete positive-half-line moment. -/
theorem integral_sq_mul_exp_neg_mul_pairedEtaLogMeasure_le
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ, t ^ 2 * Real.exp (-sigma * t) ∂pairedEtaLogMeasure) <=
      2 * sigma⁻¹ ^ 3 := by
  have hmono :
      (∫ t : ℝ, t ^ 2 * Real.exp (-sigma * t)
          ∂pairedEtaLogMeasure) <=
        ∫ t : ℝ, t ^ 2 * Real.exp (-sigma * t)
          ∂volume.restrict (Ioi 0) := by
    apply integral_mono_measure
      pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (sq_nonneg t) (Real.exp_pos _).le
    · exact integrableOn_sq_mul_exp_neg_mul_Ioi_zero hsigma
  rw [integral_sq_mul_exp_neg_mul_Ioi_zero hsigma] at hmono
  exact hmono

/-- Exact tilted-cosine cancellation bounds the total tilted mass by one half
the squared frequency times the second tilted moment. -/
theorem pairedEtaTiltedMass_le_half_sq_mul_secondMoment_of_cosine_eq_zero
    {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaTiltedCosineMoment sigma y = 0) :
    pairedEtaTiltedCosineMoment sigma 0 <=
      (y ^ 2 / 2) * ∫ t : ℝ, t ^ 2 * Real.exp (-sigma * t)
        ∂pairedEtaLogMeasure := by
  have hmass : Integrable (fun t : ℝ => Real.exp (-sigma * t))
      pairedEtaLogMeasure := by
    simpa using integrable_pairedEtaTiltedCosineKernel sigma 0 hsigma
  have hcos : Integrable (fun t : ℝ =>
      Real.exp (-sigma * t) * Real.cos (y * t))
      pairedEtaLogMeasure :=
    integrable_pairedEtaTiltedCosineKernel sigma y hsigma
  have hsecond :=
    integrable_sq_mul_exp_neg_mul_pairedEtaLogMeasure hsigma
  have hosc : Integrable (fun t : ℝ => Real.exp (-sigma * t) *
      (1 - Real.cos (y * t))) pairedEtaLogMeasure := by
    apply (hmass.sub hcos).congr
    filter_upwards with t
    change Real.exp (-sigma * t) -
        Real.exp (-sigma * t) * Real.cos (y * t) =
      Real.exp (-sigma * t) * (1 - Real.cos (y * t))
    ring
  calc
    pairedEtaTiltedCosineMoment sigma 0 =
        pairedEtaTiltedCosineMoment sigma 0 -
          pairedEtaTiltedCosineMoment sigma y := by rw [hzero, sub_zero]
    _ = ∫ t : ℝ, Real.exp (-sigma * t) -
          Real.exp (-sigma * t) * Real.cos (y * t)
          ∂pairedEtaLogMeasure := by
      rw [pairedEtaTiltedCosineMoment]
      simp only [zero_mul, Real.cos_zero, mul_one]
      rw [pairedEtaTiltedCosineMoment, integral_sub hmass hcos]
    _ = ∫ t : ℝ, Real.exp (-sigma * t) *
          (1 - Real.cos (y * t)) ∂pairedEtaLogMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ <= ∫ t : ℝ, (y ^ 2 / 2) *
          (t ^ 2 * Real.exp (-sigma * t)) ∂pairedEtaLogMeasure := by
      apply integral_mono_ae hosc (hsecond.const_mul (y ^ 2 / 2))
      filter_upwards with t
      have hquad : 1 - Real.cos (y * t) <= (y * t) ^ 2 / 2 := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := y * t)]
      calc
        Real.exp (-sigma * t) * (1 - Real.cos (y * t)) <=
            Real.exp (-sigma * t) * ((y * t) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hquad (Real.exp_pos _).le
        _ = (y ^ 2 / 2) * (t ^ 2 * Real.exp (-sigma * t)) := by
          ring
    _ = (y ^ 2 / 2) *
        ∫ t : ℝ, t ^ 2 * Real.exp (-sigma * t)
          ∂pairedEtaLogMeasure := by rw [integral_const_mul]

/-- A zero of the fixed eta Laplace transform obeys the stronger squared
vertical zero-exclusion inequality. -/
theorem sq_mul_one_sub_exp_le_sq_y_of_pairedEtaTiltedCosineMoment_eq_zero
    {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaTiltedCosineMoment sigma y = 0) :
    sigma ^ 2 * (1 - Real.exp (-sigma * Real.log 2)) <= y ^ 2 := by
  have hlower := firstIntervalMass_le_pairedEtaTiltedMass hsigma
  have hcancel :=
    pairedEtaTiltedMass_le_half_sq_mul_secondMoment_of_cosine_eq_zero
      hsigma hzero
  have hmoment :=
    integral_sq_mul_exp_neg_mul_pairedEtaLogMeasure_le hsigma
  have hchain :
      (1 - Real.exp (-sigma * Real.log 2)) / sigma <=
        (y ^ 2 / 2) * (2 * sigma⁻¹ ^ 3) :=
    hlower.trans (hcancel.trans
      (mul_le_mul_of_nonneg_left hmoment (div_nonneg (sq_nonneg y) (by norm_num))))
  calc
    sigma ^ 2 * (1 - Real.exp (-sigma * Real.log 2)) =
        sigma ^ 3 *
          ((1 - Real.exp (-sigma * Real.log 2)) / sigma) := by
      field_simp [hsigma.ne']
    _ <= sigma ^ 3 * ((y ^ 2 / 2) * (2 * sigma⁻¹ ^ 3)) :=
      mul_le_mul_of_nonneg_left hchain (pow_nonneg hsigma.le 3)
    _ = y ^ 2 := by
      field_simp [hsigma.ne']

/-- The squared exclusion is equivalently an explicit square-root lower bound
for the absolute frequency. -/
theorem sigma_mul_sqrt_one_sub_exp_le_abs_y_of_pairedEtaTiltedCosineMoment_eq_zero
    {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaTiltedCosineMoment sigma y = 0) :
    sigma * Real.sqrt (1 - Real.exp (-sigma * Real.log 2)) <= |y| := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : Real.exp (-sigma * Real.log 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hA : 0 <= 1 - Real.exp (-sigma * Real.log 2) :=
    (sub_pos.mpr hexp).le
  apply (sq_le_sq₀
    (mul_nonneg hsigma.le (Real.sqrt_nonneg _)) (abs_nonneg y)).mp
  calc
    (sigma * Real.sqrt (1 - Real.exp (-sigma * Real.log 2))) ^ 2 =
        sigma ^ 2 * (1 - Real.exp (-sigma * Real.log 2)) := by
      rw [mul_pow, Real.sq_sqrt hA]
    _ <= y ^ 2 :=
      sq_mul_one_sub_exp_le_sq_y_of_pairedEtaTiltedCosineMoment_eq_zero
        hsigma hzero
    _ = |y| ^ 2 := (sq_abs y).symm

/-- Throughout the positive half-plane the quadratic vertical threshold is
strictly stronger than the earlier linear threshold. -/
theorem etaMeasure_linear_vertical_threshold_lt_quadratic
    {sigma : ℝ} (hsigma : 0 < sigma) :
    sigma * (1 - Real.exp (-sigma * Real.log 2)) <
      sigma * Real.sqrt (1 - Real.exp (-sigma * Real.log 2)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexpLt : Real.exp (-sigma * Real.log 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hexpPos : 0 < Real.exp (-sigma * Real.log 2) := Real.exp_pos _
  apply mul_lt_mul_of_pos_left _ hsigma
  rw [Real.lt_sqrt_self_iff]
  exact ⟨(sub_pos.mpr hexpLt).ne', by linarith⟩

/-- Every nontrivial zeta zero satisfies the stronger squared eta-measure
vertical exclusion. -/
theorem nontrivialZetaZero_etaMeasure_quadratic_vertical_exclusion_sq
    (rho : NontrivialZetaZero) :
    rho.1.re ^ 2 *
        (1 - Real.exp (-rho.1.re * Real.log 2)) <= rho.1.im ^ 2 := by
  exact
    sq_mul_one_sub_exp_le_sq_y_of_pairedEtaTiltedCosineMoment_eq_zero
      (NontrivialZetaZero.zero_lt_re rho)
      (pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero rho).1

/-- Every nontrivial zeta zero satisfies the stronger square-root eta-measure
vertical exclusion. -/
theorem nontrivialZetaZero_etaMeasure_quadratic_vertical_exclusion
    (rho : NontrivialZetaZero) :
    rho.1.re *
        Real.sqrt (1 - Real.exp (-rho.1.re * Real.log 2)) <= |rho.1.im| := by
  exact
    sigma_mul_sqrt_one_sub_exp_le_abs_y_of_pairedEtaTiltedCosineMoment_eq_zero
      (NontrivialZetaZero.zero_lt_re rho)
      (pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero rho).1

end

end RiemannGaussian
