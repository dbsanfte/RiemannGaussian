import RiemannGaussian.RiemannXiFiniteVariationFrontier

/-!
# Absolute summability of the complete Blaschke logarithmic derivative

At a noncolliding upper observation point, the spectral divisor has a uniform
Euclidean gap.  The critical-strip height bound converts that gap into a
uniform positive lower bound for every elementary upper-half-plane Blaschke
factor.  The already-summable elementary derivative variation then dominates
the norms of the signed logarithmic-derivative terms.

This constructs the complete signed Blaschke logarithmic derivative as an
absolutely convergent complex series and identifies it as the limit of the
finite genuine spectral windows and reflection residuals.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A positive Euclidean gap gives a uniform lower bound for the elementary
upper-half-plane Blaschke factor. -/
theorem one_le_gapCoefficient_mul_upperHalfPlanePseudoHyperbolicDistance
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : delta ≤ ‖z - alpha‖) (halphaHalf : alpha.im ≤ 1 / 2) :
    1 ≤ (1 + 2 * z.im / delta ^ 2) *
      upperHalfPlanePseudoHyperbolicDistance z alpha := by
  let N : ℝ := Complex.normSq (z - alpha)
  let L : ℝ := Complex.normSq (z - starRingEnd ℂ alpha)
  let C : ℝ := 1 + 2 * z.im / delta ^ 2
  let r : ℝ := upperHalfPlanePseudoHyperbolicDistance z alpha
  have hN : 0 < N := by
    dsimp [N]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have hL : 0 < L := by
    dsimp [L]
    exact Complex.normSq_pos.mpr
      (sub_conj_ne_zero_of_im_pos hz halpha)
  have hgapSq : delta ^ 2 ≤ N := by
    dsimp [N]
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z - alpha)]
  have hnumLe : 4 * z.im * alpha.im ≤ 2 * z.im := by
    have hmul := mul_le_mul_of_nonneg_left halphaHalf
      (show 0 ≤ 4 * z.im by positivity)
    nlinarith
  have hLEq : L = N + 4 * z.im * alpha.im := by
    dsimp [L, N]
    unfold Complex.normSq
    simp
    ring
  have hCLower : L ≤ C * N := by
    rw [hLEq]
    dsimp [C]
    have hscale : 2 * z.im ≤ (2 * z.im / delta ^ 2) * N := by
      calc
        2 * z.im = (2 * z.im / delta ^ 2) * delta ^ 2 := by
          field_simp [hdelta.ne']
        _ ≤ (2 * z.im / delta ^ 2) * N :=
          mul_le_mul_of_nonneg_left hgapSq (by positivity)
    nlinarith
  have hrSq : r ^ 2 = N / L := by
    dsimp [r, N, L]
    unfold upperHalfPlanePseudoHyperbolicDistance
    rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
  have honeSq : 1 ≤ C * r ^ 2 := by
    rw [hrSq]
    calc
      (1 : ℝ) = L / L := by field_simp [hL.ne']
      _ ≤ (C * N) / L :=
        div_le_div_of_nonneg_right hCLower hL.le
      _ = C * (N / L) := by ring
  have hr0 : 0 ≤ r := by
    dsimp [r, upperHalfPlanePseudoHyperbolicDistance]
    positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (upperHalfPlanePseudoHyperbolicDistance_lt_one hz halpha).le
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hrSqLe : r ^ 2 ≤ r := by nlinarith
  exact honeSq.trans (mul_le_mul_of_nonneg_left hrSqLe hC0)

/-- The signed upper Blaschke logarithmic-derivative term, restricted to the
actual upper spectral divisor. -/
def zetaUpperBlaschkeSelectedLogDerivativeSummand
    (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    zetaUpperBlaschkeLogDerivativeSummand z rho
  else 0

/-- The uniform gap coefficient times elementary derivative variation
dominates the norm of every selected signed logarithmic-derivative term. -/
theorem norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_le_variation
    {z : ℂ} (hz : 0 < z.im) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      delta ≤ ‖z - zetaSpectralCoordinate rho.1‖)
    (rho : NontrivialZetaZero) :
    ‖zetaUpperBlaschkeSelectedLogDerivativeSummand z rho‖ ≤
      (1 + 2 * z.im / delta ^ 2) *
        zetaUpperBlaschkeDerivativeVariationSummand z rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha : ℂ := zetaSpectralCoordinate rho.1
    let b : ℂ → ℂ := elementaryUpperHalfPlaneBlaschke alpha
    let C : ℝ := 1 + 2 * z.im / delta ^ 2
    have hne : z ≠ alpha := by
      intro heq
      have hzero : ‖z - alpha‖ = 0 := by rw [heq, sub_self, norm_zero]
      have hpositive := hgap rho
      dsimp [alpha] at hzero hpositive
      rw [hzero] at hpositive
      linarith
    have hden : z - starRingEnd ℂ alpha ≠ 0 :=
      sub_conj_ne_zero_of_im_pos hz hupper
    have hbne : b z ≠ 0 := by
      exact div_ne_zero (sub_ne_zero.mpr hne) hden
    have hhalf : alpha.im ≤ 1 / 2 := by
      dsimp [alpha]
      have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
      exact (le_abs_self _).trans habs.le
    have hfactor : 1 ≤ C * ‖b z‖ := by
      dsimp [C, b, elementaryUpperHalfPlaneBlaschke]
      exact
        one_le_gapCoefficient_mul_upperHalfPlanePseudoHyperbolicDistance
          hz hupper hne hdelta (hgap rho) hhalf
    have hlog :
        logDeriv b z =
          1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha) :=
      logDeriv_elementaryUpperHalfPlaneBlaschke hz hupper hne
    have hderivFactor : deriv b z = b z * logDeriv b z := by
      unfold logDeriv
      simp only [Pi.div_apply]
      field_simp [hbne]
    rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_pos hupper,
      zetaUpperBlaschkeDerivativeVariationSummand, if_pos hupper]
    unfold zetaUpperBlaschkeLogDerivativeSummand
    change ‖(analyticZetaZeroMultiplicity rho : ℂ) *
        (1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha))‖ ≤
      C * ((analyticZetaZeroMultiplicity rho : ℝ) * ‖deriv b z‖)
    rw [← hlog, norm_mul, Complex.norm_natCast, hderivFactor, norm_mul]
    have hlogBound :
        ‖logDeriv b z‖ ≤ C * ‖b z‖ * ‖logDeriv b z‖ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg (logDeriv b z))
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) * ‖logDeriv b z‖ ≤
          (analyticZetaZeroMultiplicity rho : ℝ) *
            (C * ‖b z‖ * ‖logDeriv b z‖) :=
        mul_le_mul_of_nonneg_left hlogBound (Nat.cast_nonneg _)
      _ = C * ((analyticZetaZeroMultiplicity rho : ℝ) *
          (‖b z‖ * ‖logDeriv b z‖)) := by ring
  · rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_neg hupper,
      norm_zero, zetaUpperBlaschkeDerivativeVariationSummand, if_neg hupper,
      mul_zero]

/-- At every noncolliding upper point, the complete selected signed Blaschke
logarithmic-derivative series is absolutely summable. -/
theorem summable_zetaUpperBlaschkeSelectedLogDerivativeSummand
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Summable (zetaUpperBlaschkeSelectedLogDerivativeSummand z) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_zetaSpectralCoordinate_gap_of_ne_zero hxi
  apply
    ((summable_zetaUpperBlaschkeDerivativeVariationSummand hz).mul_left
      (1 + 2 * z.im / delta ^ 2)).of_norm_bounded
  intro rho
  exact
    norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_le_variation
      hz hdelta hgap rho

/-- The complete absolutely convergent signed Blaschke logarithmic derivative
of the upper spectral divisor. -/
def riemannXiUpperBlaschkeCompleteLogDerivative (z : ℂ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperBlaschkeSelectedLogDerivativeSummand z rho

/-- Restricting the selected summand to a symmetric spectral window is exactly
the existing finite upper Blaschke logarithmic-derivative window. -/
theorem sum_zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_window
    (z : ℂ) (T : ℝ) :
    ∑ rho ∈ spectralZetaZeroWindow T,
        zetaUpperBlaschkeSelectedLogDerivativeSummand z rho =
      riemannXiUpperBlaschkeLogDerivativeWindow z T := by
  unfold zetaUpperBlaschkeSelectedLogDerivativeSummand
    riemannXiUpperBlaschkeLogDerivativeWindow
    spectralUpperZetaZeroWindow
  rw [Finset.sum_filter]

/-- Cofinal genuine spectral windows converge to the complete signed
Blaschke logarithmic derivative. -/
theorem tendsto_riemannXiUpperBlaschkeLogDerivativeWindow
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (riemannXiUpperBlaschkeLogDerivativeWindow z) atTop
      (nhds (riemannXiUpperBlaschkeCompleteLogDerivative z)) := by
  unfold riemannXiUpperBlaschkeCompleteLogDerivative
  have hlimit :=
    (summable_zetaUpperBlaschkeSelectedLogDerivativeSummand hz hxi).hasSum.comp
      tendsto_spectralZetaZeroWindow_atTop
  apply hlimit.congr'
  exact Eventually.of_forall fun T =>
    sum_zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_window z T

/-- On every nonnegative window, the exact xi reflection residual is the
finite signed Blaschke logarithmic-derivative sum. -/
theorem riemannXiUpperSpectralReflectionResidual_eq_logDerivativeWindow
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : 0 ≤ T) :
    riemannXiUpperSpectralReflectionResidual z T =
      riemannXiUpperBlaschkeLogDerivativeWindow z T := by
  rw [← logDeriv_riemannXiUpperBlaschkeProductWindow_eq_reflectionResidual
      hz hxi hT,
    logDeriv_riemannXiUpperBlaschkeProductWindow_eq_sum hz hxi T]

/-- The exact finite xi reflection residuals therefore converge to the
complete absolutely convergent signed Blaschke logarithmic derivative. -/
theorem tendsto_riemannXiUpperSpectralReflectionResidual
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (riemannXiUpperSpectralReflectionResidual z) atTop
      (nhds (riemannXiUpperBlaschkeCompleteLogDerivative z)) := by
  apply (tendsto_riemannXiUpperBlaschkeLogDerivativeWindow hz hxi).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact
    (riemannXiUpperSpectralReflectionResidual_eq_logDerivativeWindow
      hz hxi hT).symm

/-- A frequently persistent lower bound on finite reflection residuals passes
to the norm of the complete signed logarithmic derivative. -/
theorem le_norm_riemannXiUpperBlaschkeCompleteLogDerivative_of_frequently_residual
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {q : ℝ}
    (hresidual : ∃ᶠ T : ℝ in atTop,
      q ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖) :
    q ≤ ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ := by
  exact ge_of_tendsto_of_frequently
    (tendsto_norm.comp
      (tendsto_riemannXiUpperSpectralReflectionResidual hz hxi))
    hresidual

/-- The direct `not RH` frontier can now be made static on its residual side:
either the complete signed Blaschke logarithmic derivative has a fixed
positive norm, or finite-window phase dispersion is eventually positive. -/
theorem fourth_variationTotal_le_completeLogDerivative_or_phaseDispersion_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hRH : ¬RiemannHypothesis) :
    riemannXiUpperBlaschkeDerivativeVariationTotal z / 4 ≤
        ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ ∨
      ∀ᶠ T : ℝ in atTop,
        (riemannXiUpperBlaschkeDerivativeVariationTotal z / 4) ^ 2 ≤
          riemannXiUpperBlaschkePhaseDispersionWindow z T := by
  rcases
      frequently_reflectionResidual_or_eventually_phaseDispersion_of_not_rh
        hz hxi hRH with hresidual | hdispersion
  · exact Or.inl
      (le_norm_riemannXiUpperBlaschkeCompleteLogDerivative_of_frequently_residual
        hz hxi hresidual)
  · exact Or.inr hdispersion

/-- Equivalently, the remaining dynamic branch is literal weighted unit-phase
chordal energy. -/
theorem fourth_variationTotal_le_completeLogDerivative_or_phaseChordEnergy_of_not_rh
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hRH : ¬RiemannHypothesis) :
    riemannXiUpperBlaschkeDerivativeVariationTotal z / 4 ≤
        ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ ∨
      ∀ᶠ T : ℝ in atTop,
        (riemannXiUpperBlaschkeDerivativeVariationTotal z / 4) ^ 2 ≤
          riemannXiUpperBlaschkePhaseChordEnergyWindow z T := by
  rcases
      fourth_variationTotal_le_completeLogDerivative_or_phaseDispersion_of_not_rh
        hz hxi hRH with hcomplete | hdispersion
  · exact Or.inl hcomplete
  · exact Or.inr
      (eventually_phaseChordEnergy_of_eventually_phaseDispersion hdispersion)

end

end RiemannGaussian
