import RiemannGaussian.EtaZeroTiltFirstCorrection

/-!
# The actual completed current's first broad-heat correction

The midpoint coefficient is integrated against the original signed current,
including the translated simple-zero head. The exact signed defect remains
an integral before its inverse-square-width error is estimated.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual completed current integrated against its physical midpoint. -/
def pairedEtaLeadingCurrentMidpointMoment (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ p : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p *
      ((p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2)
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ p : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p *
      ((p.1 + p.2) / 2)
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))

/-- The physical midpoint moment of an integrable finite-window current is integrable. -/
theorem integrable_current_midpoint {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T) {L : ℝ}
    (hwindow : ∀ᵐ p ∂μ, T p ∈ Icc 0 L ∧ p.2 ∈ Icc 0 L) :
    Integrable (fun p ↦ f p * ((T p + p.2) / 2)) μ := by
  apply hf.mul_bdd ((hT.add measurable_snd).div_const 2).aestronglyMeasurable
  filter_upwards [hwindow] with p hp
  show ‖(T p + p.2) / 2‖ ≤ L
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hp.1.1, hp.2.1])]
  linarith [hp.1.2, hp.2.2]

/-- Both actual completed-current midpoint coefficients are genuinely integrable. -/
theorem integrable_leadingCurrent_midpoint (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (fun p : ℝ × ℝ ↦ pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p *
      ((p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2))
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    Integrable (fun p : ℝ × ℝ ↦ pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p *
      ((p.1 + p.2) / 2))
      ((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))) :=
  ⟨integrable_current_midpoint (integrable_topPrefixFiniteEnergyHeadKernel rho N)
      (measurable_fst.add_const _) (ae_head_current_physical_window N),
    integrable_current_midpoint (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      measurable_fst (ae_adjacent_current_physical_window N)⟩

/-- Removing the actual midpoint term leaves an exact signed current
integral against the multiplier's first-order defect. -/
theorem normalized_current_zeroTiltGapReturn_sub_midpoint {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T) {L : ℝ}
    (hwindow : ∀ᵐ p ∂μ, T p ∈ Icc 0 L ∧ p.2 ∈ Icc 0 L) {h : ℝ} (hh : 2 ≤ h) :
    (pairedEtaZeroTiltGapNormalization h : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂μ.prod pairedEtaLogGapMeasure) - ((∫ p, f p ∂μ : ℝ) : ℂ) -
      (((∫ p, f p * ((T p + p.2) / 2) ∂μ) / (Real.sqrt Real.pi * h) : ℝ) : ℂ) =
      ∫ p, (f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 - 1 -
        ((T p + p.2) / 2) / (Real.sqrt Real.pi * h) : ℝ) ∂μ := by
  have hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2 := hwindow.mono fun _ hp ↦ ⟨hp.1.1, hp.2.1⟩
  have hiR := integrable_current_zeroTiltGapMultiplier hf hT hh
  have hiM : Integrable (fun p ↦ (f p : ℂ) * (((T p + p.2) / 2) / (Real.sqrt Real.pi * h) : ℝ)) μ := by
    apply ((integrable_current_midpoint hf hT hwindow).div_const (Real.sqrt Real.pi * h)).ofReal.congr
    filter_upwards with p
    change ((f p * ((T p + p.2) / 2) / (Real.sqrt Real.pi * h) : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    ring
  have hm : (((∫ p, f p * ((T p + p.2) / 2) ∂μ) / (Real.sqrt Real.pi * h) : ℝ) : ℂ) =
      ∫ p, (f p : ℂ) * (((T p + p.2) / 2) / (Real.sqrt Real.pi * h) : ℝ) ∂μ := by
    rw [← integral_div, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with p
    push_cast
    ring
  rw [normalized_current_zeroTiltGapReturn_eq_multiplier hf hT hpos (by linarith), hm,
    ← integral_complex_ofReal]
  calc
    _ = ∫ p, ((f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 : ℂ) - (f p : ℂ)) -
        (f p : ℂ) * (((T p + p.2) / 2) / (Real.sqrt Real.pi * h) : ℝ) ∂μ := by
      rw [integral_sub (f := fun p ↦ (f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 : ℂ) - (f p : ℂ))
        (hiR.sub hf.ofReal) hiM, integral_sub
          (f := fun p ↦ (f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 : ℂ))
          (g := fun p ↦ (f p : ℂ)) hiR hf.ofReal]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      push_cast
      ring

/-- The actual midpoint-corrected reconstruction error is uniformly
inverse-square in width on every finite physical window. -/
theorem norm_normalized_current_zeroTiltGapReturn_sub_midpoint_le
    {μ : Measure (ℝ × ℝ)} [SFinite μ] {f : ℝ × ℝ → ℝ} (hf : Integrable f μ)
    {T : ℝ × ℝ → ℝ} (hT : Measurable T) {L : ℝ}
    (hwindow : ∀ᵐ p ∂μ, T p ∈ Icc 0 L ∧ p.2 ∈ Icc 0 L) {h : ℝ} (hh : 2 ≤ h) :
    ‖(pairedEtaZeroTiltGapNormalization h : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂μ.prod pairedEtaLogGapMeasure) - ((∫ p, f p ∂μ : ℝ) : ℂ) -
      (((∫ p, f p * ((T p + p.2) / 2) ∂μ) / (Real.sqrt Real.pi * h) : ℝ) : ℂ)‖ ≤
      (∫ p, |f p| ∂μ) * (19 * (1 + L) ^ 3 / h ^ 2) := by
  rw [normalized_current_zeroTiltGapReturn_sub_midpoint hf hT hwindow hh, ← integral_mul_const]
  apply norm_integral_le_of_norm_le (hf.abs.mul_const _)
  filter_upwards [hwindow] with p hp
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pairedEtaZeroTiltGapMultiplier_firstCorrection_error_le hh hp.1 hp.2) (abs_nonneg _)

/-- The original completed current has its literal physical midpoint as
the first broad-heat coefficient in both multiplicity branches. -/
theorem pairedEtaLeadingCurrentZeroTiltGapReturn_midpoint_error_le (rho : NontrivialZetaZero) (N : ℕ)
    {h : ℝ} (hh : 2 ≤ h) :
    ‖pairedEtaLeadingCurrentZeroTiltGapReturn rho N h -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) -
      (pairedEtaLeadingCurrentMidpointMoment rho N / (Real.sqrt Real.pi * h) : ℝ)‖ ≤
      pairedEtaLeadingCurrentAbsoluteKernelMass rho N *
        (19 * (1 + pairedEtaLogTailCutoff (N + 2)) ^ 3 / h ^ 2) := by
  unfold pairedEtaLeadingCurrentZeroTiltGapReturn
  rw [(pairedEtaLeadingCurrentIntegratedGapReturn_fullHeat rho N (by norm_num : (0 : ℝ) ≤ 0)
    (by linarith : 0 < h) (phi := fun _ ↦ 0) (psi := fun _ ↦ 0) measurable_const measurable_const).2]
  unfold pairedEtaLeadingCurrentFullTwoHeatIntegral pairedEtaLeadingCurrentAbsoluteKernelMass
    pairedEtaLeadingCurrentMidpointMoment
  split_ifs with hm
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_headKernel_of_multiplicity_eq_one rho hm N]
    exact norm_normalized_current_zeroTiltGapReturn_sub_midpoint_le
      (integrable_topPrefixFiniteEnergyHeadKernel rho N) (measurable_fst.add_const _)
      (ae_head_current_physical_window N) hh
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_factoredAdjacentMomentKernel_of_two_le_multiplicity rho
      (show 2 ≤ analyticZetaZeroMultiplicity rho by have := analyticZetaZeroMultiplicity_positive rho; omega) N]
    exact norm_normalized_current_zeroTiltGapReturn_sub_midpoint_le
      (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N) measurable_fst
      (ae_adjacent_current_physical_window N) hh

/-- The actual arithmetic kernel-mass estimate makes every cutoff and
multiplicity dependence of the midpoint-corrected error explicit. -/
theorem pairedEtaLeadingCurrentZeroTiltGapReturn_midpoint_error_le_arithmetic
    (rho : NontrivialZetaZero) (N : ℕ) {h : ℝ} (hh : 2 ≤ h) :
    ‖pairedEtaLeadingCurrentZeroTiltGapReturn rho N h -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) -
      (pairedEtaLeadingCurrentMidpointMoment rho N / (Real.sqrt Real.pi * h) : ℝ)‖ ≤
      19 * pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho + 3) /
          ((N + 1 : ℝ) * h ^ 2) := by
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  calc
    _ ≤ pairedEtaLeadingCurrentAbsoluteKernelMass rho N *
        (19 * (1 + pairedEtaLogTailCutoff (N + 2)) ^ 3 / h ^ 2) :=
      pairedEtaLeadingCurrentZeroTiltGapReturn_midpoint_error_le rho N hh
    _ ≤ (pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) / (N + 1 : ℝ)) *
        (19 * (1 + pairedEtaLogTailCutoff (N + 2)) ^ 3 / h ^ 2) :=
      mul_le_mul_of_nonneg_right (pairedEtaLeadingCurrentAbsoluteKernelMass_le rho N) (by positivity)
    _ = _ := by rw [pow_add, div_mul_div_comm]; ring

end

end RiemannGaussian
