import RiemannGaussian.RiemannXiBlaschkeLogDerivativeSummability

/-!
# Complete signed variation and phase dispersion

Absolute summability of the selected signed Blaschke logarithmic-derivative
terms gives finite complete limits for their `l1` variation, cancellation,
and pairwise phase dispersion.  The finite-window dispersion identity passes
to these limits.

The resulting static invariants give a sharp rigidity formulation: at every
noncolliding upper observation point, RH is equivalent to simultaneous
vanishing of the complete signed resultant and complete phase dispersion.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Complete `l1` variation of the absolutely summable signed upper Blaschke
logarithmic-derivative terms. -/
def riemannXiUpperBlaschkeCompleteLogDerivativeVariation (z : ℂ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    ‖zetaUpperBlaschkeSelectedLogDerivativeSummand z rho‖

/-- Complete triangle-cancellation gap of the signed upper Blaschke series. -/
def riemannXiUpperBlaschkeCompleteLogDerivativeCancellation (z : ℂ) : ℝ :=
  riemannXiUpperBlaschkeCompleteLogDerivativeVariation z -
    ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖

/-- Complete pairwise phase dispersion of the signed upper Blaschke series. -/
def riemannXiUpperBlaschkeCompletePhaseDispersion (z : ℂ) : ℝ :=
  riemannXiUpperBlaschkeCompleteLogDerivativeVariation z ^ 2 -
    ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ ^ 2

/-- The complete resultant norm is bounded by complete termwise variation. -/
theorem norm_riemannXiUpperBlaschkeCompleteLogDerivative_le_variation
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ ≤
      riemannXiUpperBlaschkeCompleteLogDerivativeVariation z := by
  unfold riemannXiUpperBlaschkeCompleteLogDerivative
    riemannXiUpperBlaschkeCompleteLogDerivativeVariation
  exact norm_tsum_le_tsum_norm
    (summable_zetaUpperBlaschkeSelectedLogDerivativeSummand hz hxi).norm

/-- Complete signed-series cancellation is nonnegative. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivativeCancellation_nonneg
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    0 ≤ riemannXiUpperBlaschkeCompleteLogDerivativeCancellation z := by
  unfold riemannXiUpperBlaschkeCompleteLogDerivativeCancellation
  exact sub_nonneg.mpr
    (norm_riemannXiUpperBlaschkeCompleteLogDerivative_le_variation hz hxi)

/-- Complete phase dispersion is nonnegative. -/
theorem riemannXiUpperBlaschkeCompletePhaseDispersion_nonneg
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    0 ≤ riemannXiUpperBlaschkeCompletePhaseDispersion z := by
  have hnorm :=
    norm_riemannXiUpperBlaschkeCompleteLogDerivative_le_variation hz hxi
  have hnorm0 : 0 ≤ ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ :=
    norm_nonneg _
  unfold riemannXiUpperBlaschkeCompletePhaseDispersion
  nlinarith

/-- Exact complete factorization of phase dispersion into cancellation times
the sum of variation and resultant norm. -/
theorem riemannXiUpperBlaschkeCompletePhaseDispersion_eq_cancellation_mul_add
    (z : ℂ) :
    riemannXiUpperBlaschkeCompletePhaseDispersion z =
      riemannXiUpperBlaschkeCompleteLogDerivativeCancellation z *
        (riemannXiUpperBlaschkeCompleteLogDerivativeVariation z +
          ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖) := by
  unfold riemannXiUpperBlaschkeCompletePhaseDispersion
    riemannXiUpperBlaschkeCompleteLogDerivativeCancellation
  ring

/-- The square of complete cancellation is bounded by complete phase
dispersion. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivativeCancellation_sq_le_dispersion
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperBlaschkeCompleteLogDerivativeCancellation z ^ 2 ≤
      riemannXiUpperBlaschkeCompletePhaseDispersion z := by
  have hnorm :=
    norm_riemannXiUpperBlaschkeCompleteLogDerivative_le_variation hz hxi
  have hnorm0 : 0 ≤ ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ :=
    norm_nonneg _
  unfold riemannXiUpperBlaschkeCompleteLogDerivativeCancellation
    riemannXiUpperBlaschkeCompletePhaseDispersion
  nlinarith

/-- A finite upper window of selected term norms is exactly the existing
finite signed-term variation. -/
theorem sum_norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_variationWindow
    (z : ℂ) (T : ℝ) :
    ∑ rho ∈ spectralZetaZeroWindow T,
        ‖zetaUpperBlaschkeSelectedLogDerivativeSummand z rho‖ =
      riemannXiUpperBlaschkeLogDerivativeVariationWindow z T := by
  unfold zetaUpperBlaschkeSelectedLogDerivativeSummand
    riemannXiUpperBlaschkeLogDerivativeVariationWindow
    spectralUpperZetaZeroWindow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hupper : rho.1.re < 2⁻¹
  · simp [hupper]
  · simp [hupper]

/-- Finite signed-term variations converge to the complete `l1` variation. -/
theorem tendsto_riemannXiUpperBlaschkeLogDerivativeVariationWindow
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (riemannXiUpperBlaschkeLogDerivativeVariationWindow z) atTop
      (nhds (riemannXiUpperBlaschkeCompleteLogDerivativeVariation z)) := by
  unfold riemannXiUpperBlaschkeCompleteLogDerivativeVariation
  have hlimit :=
    (summable_zetaUpperBlaschkeSelectedLogDerivativeSummand hz hxi).norm.hasSum.comp
      tendsto_spectralZetaZeroWindow_atTop
  apply hlimit.congr'
  exact Eventually.of_forall fun T =>
    sum_norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_variationWindow
      z T

/-- Finite pairwise phase dispersion converges to the complete dispersion
invariant. -/
theorem tendsto_riemannXiUpperBlaschkePhaseDispersionWindow
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (riemannXiUpperBlaschkePhaseDispersionWindow z) atTop
      (nhds (riemannXiUpperBlaschkeCompletePhaseDispersion z)) := by
  have hvariation :=
    tendsto_riemannXiUpperBlaschkeLogDerivativeVariationWindow hz hxi
  have hsum := tendsto_riemannXiUpperBlaschkeLogDerivativeWindow hz hxi
  have hnorm := tendsto_norm.comp hsum
  have hlimit := (hvariation.mul hvariation).sub (hnorm.mul hnorm)
  have hlimit' :
      Tendsto
        (fun T =>
          riemannXiUpperBlaschkeLogDerivativeVariationWindow z T ^ 2 -
            ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖ ^ 2)
        atTop
        (nhds
          (riemannXiUpperBlaschkeCompleteLogDerivativeVariation z ^ 2 -
            ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ ^ 2)) := by
    simpa only [Function.comp_apply, pow_two] using hlimit
  unfold riemannXiUpperBlaschkeCompletePhaseDispersion
  apply hlimit'.congr'
  exact Eventually.of_forall fun T => by
    rw [riemannXiUpperBlaschkePhaseDispersionWindow_eq_variation_sq_sub_norm_sq]

/-- Pointwise, elementary derivative variation is bounded by the norm of the
selected signed logarithmic-derivative term. -/
theorem zetaUpperBlaschkeDerivativeVariationSummand_le_norm_selected
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (rho : NontrivialZetaZero) :
    zetaUpperBlaschkeDerivativeVariationSummand z rho ≤
      ‖zetaUpperBlaschkeSelectedLogDerivativeSummand z rho‖ := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_pos hupper]
    apply
      zetaUpperBlaschkeDerivativeVariationSummand_le_norm_logDerivativeSummand
        hz rho hupper
    intro heq
    apply hxi
    rw [heq]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩
  · rw [zetaUpperBlaschkeDerivativeVariationSummand, if_neg hupper,
      zetaUpperBlaschkeSelectedLogDerivativeSummand, if_neg hupper,
      norm_zero]

/-- The actual finite elementary derivative-variation total is bounded by
the complete signed-term `l1` variation. -/
theorem riemannXiUpperBlaschkeDerivativeVariationTotal_le_completeVariation
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperBlaschkeDerivativeVariationTotal z ≤
      riemannXiUpperBlaschkeCompleteLogDerivativeVariation z := by
  rw [riemannXiUpperBlaschkeDerivativeVariationTotal_eq_tsum hz]
  unfold riemannXiUpperBlaschkeCompleteLogDerivativeVariation
  exact
    (summable_zetaUpperBlaschkeDerivativeVariationSummand hz).tsum_le_tsum
      (zetaUpperBlaschkeDerivativeVariationSummand_le_norm_selected hz hxi)
      (summable_zetaUpperBlaschkeSelectedLogDerivativeSummand hz hxi).norm

/-- Static complete rigidity dichotomy: at least half of the elementary
variation total survives either in the complete signed resultant or in the
complete cancellation, whose square is bounded by phase dispersion. -/
theorem half_variationTotal_le_completeLogDerivative_or_sq_le_completeDispersion
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperBlaschkeDerivativeVariationTotal z / 2 ≤
        ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖ ∨
      (riemannXiUpperBlaschkeDerivativeVariationTotal z / 2) ^ 2 ≤
        riemannXiUpperBlaschkeCompletePhaseDispersion z := by
  let V := riemannXiUpperBlaschkeDerivativeVariationTotal z
  let L := riemannXiUpperBlaschkeCompleteLogDerivativeVariation z
  let R := ‖riemannXiUpperBlaschkeCompleteLogDerivative z‖
  have hV0 : 0 ≤ V :=
    riemannXiUpperBlaschkeDerivativeVariationTotal_nonneg z
  have hVL : V ≤ L :=
    riemannXiUpperBlaschkeDerivativeVariationTotal_le_completeVariation
      hz hxi
  by_cases hresultant : V / 2 ≤ R
  · exact Or.inl hresultant
  · right
    have hcancellation : V / 2 ≤ L - R := by
      push Not at hresultant
      linarith
    have hhalf0 : 0 ≤ V / 2 := by positivity
    have hcancel0 : 0 ≤ L - R := by
      exact
        riemannXiUpperBlaschkeCompleteLogDerivativeCancellation_nonneg
          hz hxi
    have hsquare : (V / 2) ^ 2 ≤ (L - R) ^ 2 := by nlinarith
    exact hsquare.trans
      (riemannXiUpperBlaschkeCompleteLogDerivativeCancellation_sq_le_dispersion
        hz hxi)

/-- Under RH there are no selected upper spectral zeros, so every selected
signed term vanishes. -/
theorem zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_zero_of_rh
    (hRH : RiemannHypothesis) (z : ℂ) (rho : NontrivialZetaZero) :
    zetaUpperBlaschkeSelectedLogDerivativeSummand z rho = 0 := by
  have him : (zetaSpectralCoordinate rho.1).im = 0 :=
    (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
      rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_neg]
  linarith

/-- Under RH the complete signed upper Blaschke resultant vanishes. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_eq_zero_of_rh
    (hRH : RiemannHypothesis) (z : ℂ) :
    riemannXiUpperBlaschkeCompleteLogDerivative z = 0 := by
  unfold riemannXiUpperBlaschkeCompleteLogDerivative
  simp_rw [zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_zero_of_rh hRH]
  exact tsum_zero

/-- Under RH the complete signed-term variation vanishes. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivativeVariation_eq_zero_of_rh
    (hRH : RiemannHypothesis) (z : ℂ) :
    riemannXiUpperBlaschkeCompleteLogDerivativeVariation z = 0 := by
  unfold riemannXiUpperBlaschkeCompleteLogDerivativeVariation
  simp_rw [zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_zero_of_rh hRH,
    norm_zero]
  exact tsum_zero

/-- Under RH the complete phase dispersion vanishes. -/
theorem riemannXiUpperBlaschkeCompletePhaseDispersion_eq_zero_of_rh
    (hRH : RiemannHypothesis) (z : ℂ) :
    riemannXiUpperBlaschkeCompletePhaseDispersion z = 0 := by
  rw [riemannXiUpperBlaschkeCompletePhaseDispersion,
    riemannXiUpperBlaschkeCompleteLogDerivativeVariation_eq_zero_of_rh hRH,
    riemannXiUpperBlaschkeCompleteLogDerivative_eq_zero_of_rh hRH]
  norm_num

/-- Exact finite-invariant rigidity criterion: at any noncolliding upper
point, RH is equivalent to simultaneous vanishing of the complete signed
Blaschke resultant and complete phase dispersion. -/
theorem completeLogDerivative_eq_zero_and_phaseDispersion_eq_zero_iff_rh
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    (riemannXiUpperBlaschkeCompleteLogDerivative z = 0 ∧
      riemannXiUpperBlaschkeCompletePhaseDispersion z = 0) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hresultant, hdispersion⟩
    have hfrontier :=
      half_variationTotal_le_completeLogDerivative_or_sq_le_completeDispersion
        hz hxi
    have hV0 := riemannXiUpperBlaschkeDerivativeVariationTotal_nonneg z
    have htotal :
        riemannXiUpperBlaschkeDerivativeVariationTotal z = 0 := by
      rcases hfrontier with hresultantLower | hdispersionLower
      · rw [hresultant, norm_zero] at hresultantLower
        linarith
      · rw [hdispersion] at hdispersionLower
        nlinarith [sq_nonneg
          (riemannXiUpperBlaschkeDerivativeVariationTotal z / 2)]
    exact
      (riemannXiUpperBlaschkeDerivativeVariationTotal_eq_zero_iff_rh hz).mp
        htotal
  · intro hRH
    exact
      ⟨riemannXiUpperBlaschkeCompleteLogDerivative_eq_zero_of_rh hRH z,
        riemannXiUpperBlaschkeCompletePhaseDispersion_eq_zero_of_rh hRH z⟩

end

end RiemannGaussian
