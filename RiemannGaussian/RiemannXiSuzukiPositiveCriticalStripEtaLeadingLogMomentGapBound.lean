import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentGapDefect

/-!
# Quantitative bounds for the first eta gap-moment defect

The first nonzero eta gap-moment defect is now an explicit arithmetic target.
This module resolves every gap moment into an absolutely convergent series of
integrals over the actual omitted intervals

`(log (2n+2), log (2n+3)]`.

It then computes the positive real full-half-line moment as
`n! / sigma^(n+1)` and bounds complex support and gap moments by their
positive real envelopes. Using the entire first omitted interval
`(log 2, log 3]`, Lean obtains the strict quantitative saving

`(log 3 - log 2) * (log 2)^n * exp (-sigma * log 3)`

from the full factorial bound. Specialization gives the first rigorous bound
on the exact leading gap-moment defect attached to every nontrivial zeta zero.
The estimate is one-sided and does not yet compare complementary tilts, so it
does not imply RH.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- One arbitrary-order logarithmic moment on one explicit eta gap interval. -/
def pairedEtaLogGapMomentInterval (k : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Real.log (2 * n + 2)..Real.log (2 * n + 3),
    (t : ℂ) ^ k * Complex.exp (-s * t)

/-- The arbitrary-order moment integrals over the explicit eta gap intervals
are absolutely summable. -/
theorem summable_pairedEtaLogGapMomentInterval
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaLogGapMomentInterval k s) := by
  have hint := integrable_pairedEtaLogGapMoment k hs
  rw [pairedEtaLogGapMeasure_eq_sum_restrict] at hint
  have hnorm := hint.summable_integral
  apply hnorm.of_norm_bounded
  intro n
  unfold pairedEtaLogGapMomentInterval pairedEtaLogGapInterval
  rw [intervalIntegral.integral_of_le
    (pairedEtaLogGapInterval_pos n).le]
  exact norm_integral_le_integral_norm _

/-- The complete gap moment is the literal absolutely convergent sum over
the explicit omitted logarithmic intervals. -/
theorem pairedEtaLogGapMoment_eq_tsum_interval
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    pairedEtaLogGapMoment k s =
      ∑' n : ℕ, pairedEtaLogGapMomentInterval k s n := by
  have hint := integrable_pairedEtaLogGapMoment k hs
  rw [pairedEtaLogGapMeasure_eq_sum_restrict] at hint
  unfold pairedEtaLogGapMoment
  rw [pairedEtaLogGapMeasure_eq_sum_restrict, integral_sum_measure hint]
  apply tsum_congr
  intro n
  unfold pairedEtaLogGapMomentInterval pairedEtaLogGapInterval
  exact (intervalIntegral.integral_of_le
    (pairedEtaLogGapInterval_pos n).le).symm

/-- The positive real `k`th exponential moment on the full half-line. -/
def positiveHalfLineRealLogLaplaceMoment (k : ℕ) (sigma : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-sigma * t)

/-- The full positive real moment has its elementary factorial value. -/
theorem positiveHalfLineRealLogLaplaceMoment_eq_factorial
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    positiveHalfLineRealLogLaplaceMoment k sigma =
      (k.factorial : ℝ) / sigma ^ (k + 1) := by
  unfold positiveHalfLineRealLogLaplaceMoment
  calc
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-sigma * t)) =
        ∫ t : ℝ in Ioi 0,
          t ^ (((k : ℝ) + 1) - 1) * Real.exp (-(sigma * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change t ^ k * Real.exp (-sigma * t) =
        t ^ (((k : ℝ) + 1) - 1) * Real.exp (-(sigma * t))
      rw [add_sub_cancel_right, Real.rpow_natCast]
      congr 1
      ring_nf
    _ = (1 / sigma) ^ ((k : ℝ) + 1) *
        Real.Gamma ((k : ℝ) + 1) := by
      exact Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hsigma
    _ = (k.factorial : ℝ) / sigma ^ (k + 1) := by
      rw [Real.Gamma_nat_eq_factorial]
      rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      rw [one_div_pow]
      field_simp [hsigma.ne']

/-- The positive real full-half-line moment kernel is integrable. -/
theorem integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-sigma * t)) (Ioi 0) := by
  have hcomplex := integrable_positiveHalfLineLogLaplaceMoment k
    (s := (sigma : ℂ)) (by simpa using hsigma)
  have hnorm := hcomplex.norm
  apply hnorm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  rw [norm_mul, norm_pow, norm_real, Complex.norm_exp]
  norm_num [Complex.mul_re, abs_of_pos htpos]

/-- The norm of a complex gap moment is bounded by the complete positive
real moment at the same horizontal tilt. -/
theorem norm_pairedEtaLogGapMoment_le_factorial
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaLogGapMoment k s‖ ≤
      (k.factorial : ℝ) / s.re ^ (k + 1) := by
  have hfull := integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat k hs
  have hgapReal : Integrable (fun t : ℝ ↦
      t ^ k * Real.exp (-s.re * t)) pairedEtaLogGapMeasure :=
    Integrable.mono_measure hfull
      pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero
  have hnorm :
      ‖pairedEtaLogGapMoment k s‖ ≤
        ∫ t : ℝ, t ^ k * Real.exp (-s.re * t)
          ∂pairedEtaLogGapMeasure := by
    calc
      ‖pairedEtaLogGapMoment k s‖ ≤
          ∫ t : ℝ,
            ‖(t : ℂ) ^ k * Complex.exp (-s * t)‖
              ∂pairedEtaLogGapMeasure := by
        unfold pairedEtaLogGapMoment
        exact norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, t ^ k * Real.exp (-s.re * t)
            ∂pairedEtaLogGapMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_pairedEtaLogGapSupport]
          with t ht
        have htpos : 0 < t := ht.1
        rw [norm_mul, norm_pow, norm_real, Complex.norm_exp]
        norm_num [Complex.mul_re, abs_of_pos htpos]
  calc
    ‖pairedEtaLogGapMoment k s‖ ≤
        ∫ t : ℝ, t ^ k * Real.exp (-s.re * t)
          ∂pairedEtaLogGapMeasure := hnorm
    _ ≤ ∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-s.re * t) := by
      apply integral_mono_measure
        pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (pow_nonneg ht.le k) (Real.exp_pos _).le
      · exact hfull
    _ = (k.factorial : ℝ) / s.re ^ (k + 1) :=
      positiveHalfLineRealLogLaplaceMoment_eq_factorial k hs

/-- The first omitted interval is a submeasure of the complete eta gap
measure. -/
theorem volume_restrict_firstGap_le_pairedEtaLogGapMeasure :
    volume.restrict (pairedEtaLogGapInterval 0) ≤
      pairedEtaLogGapMeasure := by
  unfold pairedEtaLogGapMeasure
  apply Measure.restrict_mono _ le_rfl
  rw [pairedEtaLogGapSupport_eq_explicit]
  intro t ht
  rw [pairedEtaExplicitLogGapSupport, mem_iUnion]
  exact ⟨0, ht⟩

/-- An explicit positive lower bound contributed by the first omitted
logarithmic interval `(log 2, log 3]`. -/
def pairedEtaFirstGapRealMomentLower (k : ℕ) (sigma : ℝ) : ℝ :=
  (Real.log 3 - Real.log 2) * (Real.log 2) ^ k *
    Real.exp (-sigma * Real.log 3)

/-- The explicit first-gap contribution is strictly positive. -/
theorem pairedEtaFirstGapRealMomentLower_pos
    (k : ℕ) (sigma : ℝ) :
    0 < pairedEtaFirstGapRealMomentLower k sigma := by
  unfold pairedEtaFirstGapRealMomentLower
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogTwoThree : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  positivity

/-- The real tilted moment on the complete gap measure dominates the explicit
first-gap lower bound. -/
theorem pairedEtaFirstGapRealMomentLower_le_gapIntegral
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    pairedEtaFirstGapRealMomentLower k sigma ≤
      ∫ t : ℝ, t ^ k * Real.exp (-sigma * t)
        ∂pairedEtaLogGapMeasure := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogThreePos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogTwoThree : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hkernelCont : Continuous (fun t : ℝ ↦
      t ^ k * Real.exp (-sigma * t)) := by fun_prop
  have hfirst :
      pairedEtaFirstGapRealMomentLower k sigma ≤
        ∫ t : ℝ in Real.log 2..Real.log 3,
          t ^ k * Real.exp (-sigma * t) := by
    unfold pairedEtaFirstGapRealMomentLower
    calc
      (Real.log 3 - Real.log 2) * (Real.log 2) ^ k *
            Real.exp (-sigma * Real.log 3) =
          ∫ _t : ℝ in Real.log 2..Real.log 3,
            (Real.log 2) ^ k * Real.exp (-sigma * Real.log 3) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring_nf
      _ ≤ ∫ t : ℝ in Real.log 2..Real.log 3,
          t ^ k * Real.exp (-sigma * t) := by
        apply intervalIntegral.integral_mono_on hlogTwoThree.le
        · exact intervalIntegrable_const
        · exact hkernelCont.intervalIntegrable _ _
        · intro t ht
          have hpow : (Real.log 2) ^ k ≤ t ^ k :=
            pow_le_pow_left₀ hlogTwoPos.le ht.1 k
          have hexp : Real.exp (-sigma * Real.log 3) ≤
              Real.exp (-sigma * t) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr hsigma.le)
          exact mul_le_mul hpow hexp (Real.exp_pos _).le
            (pow_nonneg (hlogTwoPos.le.trans ht.1) k)
  have hfull := integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat k hsigma
  have hgap : Integrable (fun t : ℝ ↦
      t ^ k * Real.exp (-sigma * t)) pairedEtaLogGapMeasure :=
    Integrable.mono_measure hfull
      pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero
  calc
    pairedEtaFirstGapRealMomentLower k sigma ≤
        ∫ t : ℝ in Real.log 2..Real.log 3,
          t ^ k * Real.exp (-sigma * t) := hfirst
    _ = ∫ t : ℝ, t ^ k * Real.exp (-sigma * t)
          ∂volume.restrict (pairedEtaLogGapInterval 0) := by
      unfold pairedEtaLogGapInterval
      norm_num
      exact intervalIntegral.integral_of_le hlogTwoThree.le
    _ ≤ ∫ t : ℝ, t ^ k * Real.exp (-sigma * t)
          ∂pairedEtaLogGapMeasure := by
      apply integral_mono_measure
        volume_restrict_firstGap_le_pairedEtaLogGapMeasure
      · filter_upwards [ae_restrict_mem measurableSet_pairedEtaLogGapSupport]
          with t ht
        exact mul_nonneg (pow_nonneg ht.1.le k) (Real.exp_pos _).le
      · exact hgap

/-- The complex eta-support moment has an explicit strict saving over the
complete positive-half-line moment, supplied by the first omitted gap. -/
theorem norm_pairedEtaLogLaplaceMoment_le_factorial_sub_firstGap
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaLogLaplaceMoment k s‖ ≤
      (k.factorial : ℝ) / s.re ^ (k + 1) -
        pairedEtaFirstGapRealMomentLower k s.re := by
  let f : ℝ → ℝ := fun t ↦ t ^ k * Real.exp (-s.re * t)
  have hfull : Integrable f (volume.restrict (Ioi 0)) :=
    integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat k hs
  have hsupport : Integrable f pairedEtaLogMeasure :=
    Integrable.mono_measure hfull
      pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
  have hgap : Integrable f pairedEtaLogGapMeasure :=
    Integrable.mono_measure hfull
      pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero
  have hsplit :
      (∫ t : ℝ, f t ∂volume.restrict (Ioi 0)) =
        (∫ t : ℝ, f t ∂pairedEtaLogMeasure) +
          ∫ t : ℝ, f t ∂pairedEtaLogGapMeasure := by
    rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure,
      integral_add_measure hsupport hgap]
  have hnorm : ‖pairedEtaLogLaplaceMoment k s‖ ≤
      ∫ t : ℝ, f t ∂pairedEtaLogMeasure := by
    calc
      ‖pairedEtaLogLaplaceMoment k s‖ ≤
          ∫ t : ℝ, ‖(t : ℂ) ^ k * Complex.exp (-s * t)‖
            ∂pairedEtaLogMeasure := by
        unfold pairedEtaLogLaplaceMoment
        exact norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, f t ∂pairedEtaLogMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_pairedEtaLogSupport]
          with t ht
        have htpos : 0 < t := pairedEtaLogSupport_subset_Ioi_zero ht
        rw [norm_mul, norm_pow, norm_real, Complex.norm_exp]
        norm_num [f, Complex.mul_re, abs_of_pos htpos]
  have hgapLower :=
    pairedEtaFirstGapRealMomentLower_le_gapIntegral k hs
  calc
    ‖pairedEtaLogLaplaceMoment k s‖ ≤
        ∫ t : ℝ, f t ∂pairedEtaLogMeasure := hnorm
    _ = (∫ t : ℝ, f t ∂volume.restrict (Ioi 0)) -
        ∫ t : ℝ, f t ∂pairedEtaLogGapMeasure :=
      eq_sub_of_add_eq hsplit.symm
    _ ≤ (∫ t : ℝ, f t ∂volume.restrict (Ioi 0)) -
        pairedEtaFirstGapRealMomentLower k s.re :=
      sub_le_sub_left hgapLower _
    _ = (k.factorial : ℝ) / s.re ^ (k + 1) -
        pairedEtaFirstGapRealMomentLower k s.re := by
      rw [← positiveHalfLineRealLogLaplaceMoment,
        positiveHalfLineRealLogLaplaceMoment_eq_factorial k hs]

/-- The eta-support moment is strictly smaller than the complete positive
real moment, with the strictness witnessed by the first omitted interval. -/
theorem norm_pairedEtaLogLaplaceMoment_lt_factorial
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaLogLaplaceMoment k s‖ <
      (k.factorial : ℝ) / s.re ^ (k + 1) := by
  calc
    ‖pairedEtaLogLaplaceMoment k s‖ ≤
        (k.factorial : ℝ) / s.re ^ (k + 1) -
          pairedEtaFirstGapRealMomentLower k s.re :=
      norm_pairedEtaLogLaplaceMoment_le_factorial_sub_firstGap k hs
    _ < (k.factorial : ℝ) / s.re ^ (k + 1) :=
      sub_lt_self _ (pairedEtaFirstGapRealMomentLower_pos k s.re)

/-- At a zeta zero, the first nonzero arithmetic gap-moment defect satisfies
the explicit first-gap saving bound. -/
theorem norm_pairedEtaLeadingLogGapMomentDefect_le_firstGap
    (rho : NontrivialZetaZero) :
    ‖((analyticZetaZeroMultiplicity rho).factorial : ℂ) *
          (rho.1 ^ (analyticZetaZeroMultiplicity rho + 1))⁻¹ -
        pairedEtaLogGapMoment (analyticZetaZeroMultiplicity rho) rho.1‖ ≤
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
          rho.1.re ^ (analyticZetaZeroMultiplicity rho + 1) -
        pairedEtaFirstGapRealMomentLower
          (analyticZetaZeroMultiplicity rho) rho.1.re := by
  rw [← pairedEtaLogLaplaceMoment_eq_factorial_sub_gap
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)]
  exact norm_pairedEtaLogLaplaceMoment_le_factorial_sub_firstGap
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)

/-- In particular, the leading gap-moment defect is strictly smaller than
the complete positive real moment at the same horizontal tilt. -/
theorem norm_pairedEtaLeadingLogGapMomentDefect_lt_factorial
    (rho : NontrivialZetaZero) :
    ‖((analyticZetaZeroMultiplicity rho).factorial : ℂ) *
          (rho.1 ^ (analyticZetaZeroMultiplicity rho + 1))⁻¹ -
        pairedEtaLogGapMoment (analyticZetaZeroMultiplicity rho) rho.1‖ <
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
        rho.1.re ^ (analyticZetaZeroMultiplicity rho + 1) := by
  rw [← pairedEtaLogLaplaceMoment_eq_factorial_sub_gap
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)]
  exact norm_pairedEtaLogLaplaceMoment_lt_factorial
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)

end

end RiemannGaussian
