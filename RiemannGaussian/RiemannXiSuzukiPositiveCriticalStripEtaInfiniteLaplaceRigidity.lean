import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure

/-!
# A first quantitative zero constraint from the infinite eta measure

The fixed positive paired-eta logarithmic measure gives more than an exact
representation of the zeta divisor.  This module extracts a direct
quantitative consequence of its Fourier cancellation.

The measure contains the whole first interval `(0, log 2]` and is dominated
by Lebesgue measure on the positive half-line.  Its exponentially tilted mass
is therefore bounded below by the mass of that first interval, while its
first tilted moment is bounded above by the corresponding complete
exponential moment.  The elementary Lipschitz estimate

`1 - cos (y t) <= |y| t`

then turns exact cosine cancellation into an explicit zero-exclusion
inequality.  At every nontrivial zeta zero `rho`, Lean proves

`rho.re * (1 - exp (-rho.re * log 2)) <= |rho.im|`.

This is the first zero-location inequality derived directly from the one
fixed positive eta measure.  It is far too weak to imply RH, but unlike an RH
equivalence it is an unconditional restriction on every zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The fixed paired-eta measure is dominated by Lebesgue measure restricted
to the positive half-line. -/
theorem pairedEtaLogMeasure_le_volume_restrict_Ioi_zero :
    pairedEtaLogMeasure <= volume.restrict (Ioi 0) := by
  unfold pairedEtaLogMeasure
  exact Measure.restrict_mono
    pairedEtaLogSupport_subset_Ioi_zero le_rfl

/-- The first exponentially tilted Lebesgue moment is integrable on the
positive half-line. -/
theorem integrableOn_mul_exp_neg_mul_Ioi_zero
    {sigma : ℝ} (hsigma : 0 < sigma) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-sigma * t)) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    have hgamma :=
      Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num)
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    norm_num [Real.rpow_one, mul_comm]
  have hscaled : IntegrableOn
      (fun t : ℝ => (sigma * t) * Real.exp (-(sigma * t))) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => u * Real.exp (-u)) 0 hsigma).2 (by
        simpa using hbase)
  have hconst := hscaled.const_mul sigma⁻¹
  apply hconst.congr
  filter_upwards with t
  field_simp [hsigma.ne']

/-- The complete first exponential moment on the positive half-line has its
elementary exact value. -/
theorem integral_mul_exp_neg_mul_Ioi_zero
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-sigma * t)) = sigma⁻¹ ^ 2 := by
  calc
    (∫ t : ℝ in Ioi 0, t * Real.exp (-sigma * t)) =
        ∫ t : ℝ in Ioi 0,
          t ^ ((2 : ℝ) - 1) * Real.exp (-(sigma * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      norm_num [Real.rpow_one]
    _ = sigma⁻¹ ^ 2 := by
      simpa [one_div, mul_comm] using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi
          (a := (2 : ℝ)) (r := sigma) (by norm_num) hsigma)

/-- The exponential mass of the first logarithmic interval is explicit. -/
theorem integral_exp_neg_mul_Ioc_zero_log_two
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ in Ioc 0 (Real.log 2), Real.exp (-sigma * t)) =
      (1 - Real.exp (-sigma * Real.log 2)) / sigma := by
  rw [← intervalIntegral.integral_of_le (Real.log_pos one_lt_two).le]
  calc
    (∫ t : ℝ in 0..Real.log 2, Real.exp (-sigma * t)) =
        ∫ t : ℝ in 0..Real.log 2, Real.exp ((-sigma) * t) := by
          apply intervalIntegral.integral_congr
          intro t _
          congr 1
    _ = (-sigma)⁻¹ *
        ∫ u : ℝ in (-sigma) * 0..(-sigma) * Real.log 2,
          Real.exp u := by
      simpa [smul_eq_mul] using
        (intervalIntegral.integral_comp_mul_left
          (f := fun u : ℝ => Real.exp u)
          (a := (0 : ℝ)) (b := Real.log 2)
          (c := -sigma) (neg_ne_zero.mpr hsigma.ne'))
    _ = (1 - Real.exp (-sigma * Real.log 2)) / sigma := by
      rw [integral_exp]
      simp only [mul_zero, Real.exp_zero]
      field_simp [hsigma.ne']
      ring

/-- The full tilted mass of the fixed eta measure dominates the explicit
mass carried by its first interval. -/
theorem firstIntervalMass_le_pairedEtaTiltedMass
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (1 - Real.exp (-sigma * Real.log 2)) / sigma <=
      pairedEtaTiltedCosineMoment sigma 0 := by
  have hmeasure : volume.restrict (Ioc 0 (Real.log 2)) <=
      pairedEtaLogMeasure := by
    unfold pairedEtaLogMeasure
    exact Measure.restrict_mono
      Ioc_zero_log_two_subset_pairedEtaLogSupport le_rfl
  have hint : Integrable (fun t : ℝ => Real.exp (-sigma * t))
      pairedEtaLogMeasure := by
    simpa using integrable_pairedEtaTiltedCosineKernel sigma 0 hsigma
  have hmono :
      (∫ t : ℝ, Real.exp (-sigma * t)
          ∂volume.restrict (Ioc 0 (Real.log 2))) <=
        ∫ t : ℝ, Real.exp (-sigma * t) ∂pairedEtaLogMeasure := by
    exact integral_mono_measure hmeasure
      (Eventually.of_forall fun _ => (Real.exp_pos _).le) hint
  rw [integral_exp_neg_mul_Ioc_zero_log_two hsigma] at hmono
  simpa [pairedEtaTiltedCosineMoment] using hmono

/-- The first tilted moment of the fixed eta measure is integrable. -/
theorem integrable_mul_exp_neg_mul_pairedEtaLogMeasure
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Integrable (fun t : ℝ => t * Real.exp (-sigma * t))
      pairedEtaLogMeasure := by
  exact Integrable.mono_measure
    (μ := pairedEtaLogMeasure) (ν := volume.restrict (Ioi 0))
    (integrableOn_mul_exp_neg_mul_Ioi_zero hsigma)
    pairedEtaLogMeasure_le_volume_restrict_Ioi_zero

/-- The first tilted moment of the fixed eta measure is bounded above by the
complete positive-half-line exponential moment. -/
theorem integral_mul_exp_neg_mul_pairedEtaLogMeasure_le
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ, t * Real.exp (-sigma * t) ∂pairedEtaLogMeasure) <=
      sigma⁻¹ ^ 2 := by
  have hmono :
      (∫ t : ℝ, t * Real.exp (-sigma * t) ∂pairedEtaLogMeasure) <=
        ∫ t : ℝ, t * Real.exp (-sigma * t)
          ∂volume.restrict (Ioi 0) := by
    apply integral_mono_measure
      pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg ht.le (Real.exp_pos _).le
    · exact integrableOn_mul_exp_neg_mul_Ioi_zero hsigma
  rw [integral_mul_exp_neg_mul_Ioi_zero hsigma] at hmono
  exact hmono

/-- Exact tilted-cosine cancellation bounds the total tilted mass by the
frequency times the first tilted moment. -/
theorem pairedEtaTiltedMass_le_abs_mul_firstMoment_of_cosine_eq_zero
    {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaTiltedCosineMoment sigma y = 0) :
    pairedEtaTiltedCosineMoment sigma 0 <=
      |y| * ∫ t : ℝ, t * Real.exp (-sigma * t)
        ∂pairedEtaLogMeasure := by
  have hmass : Integrable (fun t : ℝ => Real.exp (-sigma * t))
      pairedEtaLogMeasure := by
    simpa using integrable_pairedEtaTiltedCosineKernel sigma 0 hsigma
  have hcos : Integrable (fun t : ℝ =>
      Real.exp (-sigma * t) * Real.cos (y * t))
      pairedEtaLogMeasure :=
    integrable_pairedEtaTiltedCosineKernel sigma y hsigma
  have hfirst := integrable_mul_exp_neg_mul_pairedEtaLogMeasure hsigma
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
    _ <= ∫ t : ℝ, |y| *
          (t * Real.exp (-sigma * t)) ∂pairedEtaLogMeasure := by
      apply integral_mono_ae hosc (hfirst.const_mul |y|)
      rw [pairedEtaLogMeasure]
      filter_upwards [ae_restrict_mem measurableSet_pairedEtaLogSupport]
        with t ht
      have htpos : 0 < t := pairedEtaLogSupport_subset_Ioi_zero ht
      have hoscNonneg : 0 <= 1 - Real.cos (y * t) :=
        sub_nonneg.mpr (Real.cos_le_one _)
      have hosc : 1 - Real.cos (y * t) <= |y| * t := by
        calc
          1 - Real.cos (y * t) = |1 - Real.cos (y * t)| :=
            (abs_of_nonneg hoscNonneg).symm
          _ = |Real.cos (y * t) - Real.cos 0| := by
            rw [Real.cos_zero, abs_sub_comm]
          _ <= |y * t - 0| := Real.abs_cos_sub_cos_le _ _
          _ = |y| * t := by rw [sub_zero, abs_mul, abs_of_pos htpos]
      calc
        Real.exp (-sigma * t) * (1 - Real.cos (y * t)) <=
            Real.exp (-sigma * t) * (|y| * t) :=
          mul_le_mul_of_nonneg_left hosc (Real.exp_pos _).le
        _ = |y| * (t * Real.exp (-sigma * t)) := by ring
    _ = |y| * ∫ t : ℝ, t * Real.exp (-sigma * t)
          ∂pairedEtaLogMeasure := by rw [integral_const_mul]

/-- A zero of the fixed eta Laplace transform obeys an explicit vertical
zero-exclusion inequality. -/
theorem sigma_mul_one_sub_exp_le_abs_y_of_pairedEtaTiltedCosineMoment_eq_zero
    {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaTiltedCosineMoment sigma y = 0) :
    sigma * (1 - Real.exp (-sigma * Real.log 2)) <= |y| := by
  have hlower := firstIntervalMass_le_pairedEtaTiltedMass hsigma
  have hcancel :=
    pairedEtaTiltedMass_le_abs_mul_firstMoment_of_cosine_eq_zero
      hsigma hzero
  have hmoment :=
    integral_mul_exp_neg_mul_pairedEtaLogMeasure_le hsigma
  have hchain :
      (1 - Real.exp (-sigma * Real.log 2)) / sigma <=
        |y| * sigma⁻¹ ^ 2 :=
    hlower.trans (hcancel.trans
      (mul_le_mul_of_nonneg_left hmoment (abs_nonneg y)))
  calc
    sigma * (1 - Real.exp (-sigma * Real.log 2)) =
        sigma ^ 2 *
          ((1 - Real.exp (-sigma * Real.log 2)) / sigma) := by
      field_simp [hsigma.ne']
    _ <= sigma ^ 2 * (|y| * sigma⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left hchain (sq_nonneg sigma)
    _ = |y| := by
      field_simp [hsigma.ne']

/-- Every nontrivial zeta zero satisfies the direct eta-measure vertical
exclusion inequality. -/
theorem nontrivialZetaZero_etaMeasure_vertical_exclusion
    (rho : NontrivialZetaZero) :
    rho.1.re *
        (1 - Real.exp (-rho.1.re * Real.log 2)) <= |rho.1.im| := by
  exact
    sigma_mul_one_sub_exp_le_abs_y_of_pairedEtaTiltedCosineMoment_eq_zero
      (NontrivialZetaZero.zero_lt_re rho)
      (pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero rho).1

/-- In particular, the fixed positive eta measure excludes real nontrivial
zeta zeros. -/
theorem nontrivialZetaZero_im_ne_zero_of_etaMeasure
    (rho : NontrivialZetaZero) : rho.1.im ≠ 0 := by
  have hre := NontrivialZetaZero.zero_lt_re rho
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : Real.exp (-rho.1.re * Real.log 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hleft : 0 < rho.1.re *
      (1 - Real.exp (-rho.1.re * Real.log 2)) :=
    mul_pos hre (sub_pos.mpr hexp)
  have hbound := nontrivialZetaZero_etaMeasure_vertical_exclusion rho
  exact abs_pos.mp (hleft.trans_le hbound)

end

end RiemannGaussian
