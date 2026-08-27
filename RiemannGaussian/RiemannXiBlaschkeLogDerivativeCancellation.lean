import RiemannGaussian.RiemannXiBlaschkeDerivativeVariation

/-!
# Finite spectral Blaschke logarithmic derivative and cancellation

The Poisson mass is total elementary Blaschke derivative variation.  Here the
same genuine upper spectral zeros, with analytic multiplicity, are assembled
into one finite Blaschke product.  Its logarithmic derivative is proved to be
the signed paired Cauchy sum.  The difference between the sum of the norms of
those terms and the norm of their sum is then isolated as an explicit
nonnegative cancellation gap.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The upper spectral zeros lying in one finite symmetric window. -/
def spectralUpperZetaZeroWindow (T : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow T).filter fun rho =>
    0 < (zetaSpectralCoordinate rho.1).im

@[simp]
theorem mem_spectralUpperZetaZeroWindow
    {T : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ spectralUpperZetaZeroWindow T ↔
      rho ∈ spectralZetaZeroWindow T ∧
        0 < (zetaSpectralCoordinate rho.1).im := by
  simp [spectralUpperZetaZeroWindow]

/-- The signed paired Cauchy logarithmic-derivative term belonging to one
upper spectral zero. -/
def zetaUpperBlaschkeLogDerivativeSummand
    (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) *
    (1 / (z - zetaSpectralCoordinate rho.1) -
      1 / (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)))

/-- Exact logarithmic derivative of one elementary Blaschke factor. -/
theorem logDeriv_elementaryUpperHalfPlaneBlaschke
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    logDeriv (elementaryUpperHalfPlaneBlaschke alpha) z =
      1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha) := by
  have hnum : z - alpha ≠ 0 := sub_ne_zero.mpr hne
  have hden : z - starRingEnd ℂ alpha ≠ 0 :=
    sub_conj_ne_zero_of_im_pos hz halpha
  rw [logDeriv_apply,
    deriv_elementaryUpperHalfPlaneBlaschke hden]
  unfold elementaryUpperHalfPlaneBlaschke
  field_simp [hnum, hden]
  ring

/-- The finite upper spectral Blaschke product, with every zero repeated by
its genuine analytic multiplicity. -/
def riemannXiUpperBlaschkeProductWindow (T : ℝ) (z : ℂ) : ℂ :=
  ∏ rho ∈ spectralUpperZetaZeroWindow T,
    elementaryUpperHalfPlaneBlaschke
        (zetaSpectralCoordinate rho.1) z ^
      analyticZetaZeroMultiplicity rho

/-- The signed paired Cauchy sum over one upper spectral window. -/
def riemannXiUpperBlaschkeLogDerivativeWindow (z : ℂ) (T : ℝ) : ℂ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    zetaUpperBlaschkeLogDerivativeSummand z rho

/-- At a noncolliding upper observation point, the signed Cauchy sum is
literally the logarithmic derivative of the finite spectral Blaschke product.
-/
theorem logDeriv_riemannXiUpperBlaschkeProductWindow_eq_sum
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) (T : ℝ) :
    logDeriv (riemannXiUpperBlaschkeProductWindow T) z =
      riemannXiUpperBlaschkeLogDerivativeWindow z T := by
  unfold riemannXiUpperBlaschkeProductWindow
    riemannXiUpperBlaschkeLogDerivativeWindow
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hne : z ≠ zetaSpectralCoordinate rho.1 := by
      intro heq
      apply hxi
      rw [heq]
      exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩
    have hden :
        z - starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ 0 :=
      sub_conj_ne_zero_of_im_pos hz hupper
    have hdiff : DifferentiableAt ℂ
        (elementaryUpperHalfPlaneBlaschke
          (zetaSpectralCoordinate rho.1)) z := by
      unfold elementaryUpperHalfPlaneBlaschke
      fun_prop
    rw [logDeriv_fun_pow hdiff,
      logDeriv_elementaryUpperHalfPlaneBlaschke hz hupper hne]
    rfl
  · intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hne : z ≠ zetaSpectralCoordinate rho.1 := by
      intro heq
      apply hxi
      rw [heq]
      exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩
    have hden :
        z - starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ 0 :=
      sub_conj_ne_zero_of_im_pos hz hupper
    exact pow_ne_zero _ (div_ne_zero (sub_ne_zero.mpr hne) hden)
  · intro rho hrho
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hden :
        z - starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ 0 :=
      sub_conj_ne_zero_of_im_pos hz hupper
    apply DifferentiableAt.pow
    unfold elementaryUpperHalfPlaneBlaschke
    fun_prop

/-- The elementary derivative variation is bounded by the norm of its signed
Blaschke logarithmic-derivative term.  The only loss is the contractive norm
of the elementary factor itself. -/
theorem zetaUpperBlaschkeDerivativeVariationSummand_le_norm_logDerivativeSummand
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im)
    (hne : z ≠ zetaSpectralCoordinate rho.1) :
    zetaUpperBlaschkeDerivativeVariationSummand z rho ≤
      ‖zetaUpperBlaschkeLogDerivativeSummand z rho‖ := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let b : ℂ → ℂ := elementaryUpperHalfPlaneBlaschke alpha
  have hden : z - starRingEnd ℂ alpha ≠ 0 :=
    sub_conj_ne_zero_of_im_pos hz hupper
  have hbne : b z ≠ 0 := by
    exact div_ne_zero (sub_ne_zero.mpr hne) hden
  have hbNorm : ‖b z‖ ≤ 1 := by
    exact (upperHalfPlanePseudoHyperbolicDistance_lt_one hz hupper).le
  have hlog :
      logDeriv b z =
        1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha) :=
    logDeriv_elementaryUpperHalfPlaneBlaschke hz hupper hne
  have hderivFactor : deriv b z = b z * logDeriv b z := by
    unfold logDeriv
    simp only [Pi.div_apply]
    field_simp [hbne]
  unfold zetaUpperBlaschkeDerivativeVariationSummand
    zetaUpperBlaschkeLogDerivativeSummand
  rw [if_pos hupper]
  change (analyticZetaZeroMultiplicity rho : ℝ) * ‖deriv b z‖ ≤
    ‖(analyticZetaZeroMultiplicity rho : ℂ) *
      (1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha))‖
  rw [← hlog, norm_mul, Complex.norm_natCast]
  calc
    (analyticZetaZeroMultiplicity rho : ℝ) * ‖deriv b z‖ =
        (analyticZetaZeroMultiplicity rho : ℝ) *
          ‖b z * logDeriv b z‖ := by rw [hderivFactor]
    _ = (analyticZetaZeroMultiplicity rho : ℝ) *
        (‖b z‖ * ‖logDeriv b z‖) := by rw [norm_mul]
    _ ≤ (analyticZetaZeroMultiplicity rho : ℝ) *
        (1 * ‖logDeriv b z‖) := by
      gcongr
    _ = (analyticZetaZeroMultiplicity rho : ℝ) *
        ‖logDeriv b z‖ := by ring

/-- The `l1` variation of the signed Cauchy logarithmic-derivative terms in
one finite upper spectral window. -/
def riemannXiUpperBlaschkeLogDerivativeVariationWindow
    (z : ℂ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    ‖zetaUpperBlaschkeLogDerivativeSummand z rho‖

/-- The elementary derivative variation in a finite window is bounded by the
`l1` variation of its signed logarithmic-derivative terms. -/
theorem riemannXiUpperBlaschkeDerivativeVariationWindow_le_ofReal_logDerivativeVariation
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) (T : ℝ) :
    riemannXiUpperBlaschkeDerivativeVariationWindow z T ≤
      ENNReal.ofReal
        (riemannXiUpperBlaschkeLogDerivativeVariationWindow z T) := by
  unfold riemannXiUpperBlaschkeDerivativeVariationWindow
    riemannXiUpperBlaschkeLogDerivativeVariationWindow
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun _rho _hrho => norm_nonneg _)]
  have hrestrict :
      (∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal
            (zetaUpperBlaschkeDerivativeVariationSummand z rho)) =
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          ENNReal.ofReal
            (zetaUpperBlaschkeDerivativeVariationSummand z rho) := by
    rw [spectralUpperZetaZeroWindow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro rho _hrho
    by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
    · rw [if_pos hupper]
    · rw [if_neg hupper,
        zetaUpperBlaschkeDerivativeVariationSummand, if_neg hupper,
        ENNReal.ofReal_zero]
  rw [hrestrict]
  apply Finset.sum_le_sum
  intro rho hrho
  apply ENNReal.ofReal_le_ofReal
  have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
  apply
    zetaUpperBlaschkeDerivativeVariationSummand_le_norm_logDerivativeSummand
      hz rho hupper
  intro heq
  apply hxi
  rw [heq]
  exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩

/-- The norm of the signed sum is at most its termwise variation. -/
theorem norm_riemannXiUpperBlaschkeLogDerivativeWindow_le_variation
    (z : ℂ) (T : ℝ) :
    ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖ ≤
      riemannXiUpperBlaschkeLogDerivativeVariationWindow z T := by
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
    riemannXiUpperBlaschkeLogDerivativeVariationWindow
  exact norm_sum_le _ _

/-- The finite signed logarithmic-derivative cancellation gap. -/
def riemannXiUpperBlaschkeLogDerivativeCancellation
    (z : ℂ) (T : ℝ) : ℝ :=
  riemannXiUpperBlaschkeLogDerivativeVariationWindow z T -
    ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖

/-- The cancellation gap is nonnegative. -/
theorem riemannXiUpperBlaschkeLogDerivativeCancellation_nonneg
    (z : ℂ) (T : ℝ) :
    0 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  unfold riemannXiUpperBlaschkeLogDerivativeCancellation
  exact sub_nonneg.mpr
    (norm_riemannXiUpperBlaschkeLogDerivativeWindow_le_variation z T)

/-- Exact decomposition of total signed-term variation into resultant norm
and cancellation. -/
theorem riemannXiUpperBlaschkeLogDerivativeVariationWindow_eq_norm_add_cancellation
    (z : ℂ) (T : ℝ) :
    riemannXiUpperBlaschkeLogDerivativeVariationWindow z T =
      ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖ +
        riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  unfold riemannXiUpperBlaschkeLogDerivativeCancellation
  linarith

/-- At a noncolliding upper point, the same identity is stated directly in
terms of the logarithmic derivative of the finite spectral Blaschke product.
-/
theorem riemannXiUpperBlaschkeLogDerivativeVariationWindow_eq_product_norm_add_cancellation
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) (T : ℝ) :
    riemannXiUpperBlaschkeLogDerivativeVariationWindow z T =
      ‖logDeriv (riemannXiUpperBlaschkeProductWindow T) z‖ +
        riemannXiUpperBlaschkeLogDerivativeCancellation z T := by
  rw [logDeriv_riemannXiUpperBlaschkeProductWindow_eq_sum hz hxi T]
  exact
    riemannXiUpperBlaschkeLogDerivativeVariationWindow_eq_norm_add_cancellation
      z T

/-- The finite Poisson defect is controlled by the resultant finite-product
logarithmic derivative plus the explicit cancellation gap.  This theorem
pinpoints the remaining rigidity problem without assuming cancellation is
small. -/
theorem riemannXiUpperHyperbolicPoissonDefectWindow_le_productLogDeriv_add_cancellation
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) (T : ℝ) :
    riemannXiUpperHyperbolicPoissonDefectWindow z T ≤
      ENNReal.ofReal (2 * z.im) *
        ENNReal.ofReal
          (‖logDeriv (riemannXiUpperBlaschkeProductWindow T) z‖ +
            riemannXiUpperBlaschkeLogDerivativeCancellation z T) := by
  rw [riemannXiUpperHyperbolicPoissonDefectWindow_eq_two_im_mul_variation
    hz T]
  calc
    ENNReal.ofReal (2 * z.im) *
          riemannXiUpperBlaschkeDerivativeVariationWindow z T ≤
        ENNReal.ofReal (2 * z.im) *
          ENNReal.ofReal
            (riemannXiUpperBlaschkeLogDerivativeVariationWindow z T) :=
      mul_le_mul_of_nonneg_left
        (riemannXiUpperBlaschkeDerivativeVariationWindow_le_ofReal_logDerivativeVariation
          hz hxi T) (by positivity)
    _ = ENNReal.ofReal (2 * z.im) *
        ENNReal.ofReal
          (‖logDeriv (riemannXiUpperBlaschkeProductWindow T) z‖ +
            riemannXiUpperBlaschkeLogDerivativeCancellation z T) := by
      rw [
        riemannXiUpperBlaschkeLogDerivativeVariationWindow_eq_product_norm_add_cancellation
          hz hxi T]

end

end RiemannGaussian
