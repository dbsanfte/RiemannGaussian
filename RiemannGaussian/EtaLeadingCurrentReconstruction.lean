import RiemannGaussian.EtaBroadGapReturn

/-!
# Reconstruction of the original completed eta leading current

The full ordered return first reconstructs the literal current with a
positive endpoint tilt. Removing that tilt then recovers the original
leading flux in both multiplicity branches. These are iterated limits for
each actual zero and arithmetic cutoff. They do not exchange the limits
with the unsolved cutoff-weighted absolute series.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The original multiplicity-selected current with a common endpoint tilt.
The head time is restored before applying the tilt. -/
def pairedEtaLeadingCurrentTiltedIntegral (rho : NontrivialZetaZero) (N : ℕ) (a : ℝ) : ℂ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
      (Real.exp (-a * (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2) : ℂ)
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
      (Real.exp (-a * (p.1 + p.2) / 2) : ℂ)
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))

/-- The exact amplitude and positive gap mass normalize the literal
integrated return. All completion and multiplicity factors remain inside it. -/
def pairedEtaLeadingCurrentNormalizedGapReturn (rho : NontrivialZetaZero) (N : ℕ) (a h : ℝ) : ℂ :=
  (((pairedEtaHeatTransitionAmplitude h) ^ 2 / pairedEtaGapLaplaceMass a : ℝ) : ℂ) *
    pairedEtaLeadingCurrentIntegratedGapReturn rho N a h a h (fun _ ↦ 0) (fun _ ↦ 0)

/-- At fixed positive tilt, broad actual heat reconstructs exactly the
tilted leading current on either literal multiplicity carrier. -/
theorem pairedEtaLeadingCurrentNormalizedGapReturn_tendsto
    (rho : NontrivialZetaZero) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (pairedEtaLeadingCurrentNormalizedGapReturn rho N a) atTop
      (𝓝 (pairedEtaLeadingCurrentTiltedIntegral rho N a)) := by
  have heq : ∀ᶠ h : ℝ in atTop,
      pairedEtaLeadingCurrentIntegratedGapReturn rho N a h a h (fun _ ↦ 0) (fun _ ↦ 0) =
      if analyticZetaZeroMultiplicity rho = 1 then
        ∫ z : (ℝ × ℝ) × ℝ, (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z.1 : ℂ) *
          pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0)
            (z.1.1 + pairedEtaLogTailCutoff (N + 1)) z.1.2 z.2
          ∂(((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod
            pairedEtaLogGapMeasure)
      else
        ∫ z : (ℝ × ℝ) × ℝ, (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z.1 : ℂ) *
          pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0) z.1.1 z.1.2 z.2
          ∂(((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod
            pairedEtaLogGapMeasure) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh
    exact pairedEtaLeadingCurrentIntegratedGapReturn_eq_prod rho N ha.le hh ha.le hh
      (by linarith) measurable_const measurable_const
  unfold pairedEtaLeadingCurrentTiltedIntegral
  split_ifs with hm
  · have hpos : ∀ᵐ p : ℝ × ℝ ∂(pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)),
        0 ≤ p.1 + pairedEtaLogTailCutoff (N + 1) ∧ 0 ≤ p.2 := by
      filter_upwards [ae_pair_mem_pairedEtaLogSupport_headMeasure N] with p hp
      exact ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, (pairedEtaLogSupport_subset_Ioi_zero hp.2).le⟩
    apply (normalized_integral_current_gapReturn_tendsto
      (integrable_topPrefixFiniteEnergyHeadKernel rho N) (measurable_fst.add_const _) hpos ha).congr'
    filter_upwards [heq] with h hh
    simp only [pairedEtaLeadingCurrentNormalizedGapReturn, hh, if_pos hm]
  · have hpos : ∀ᵐ p : ℝ × ℝ ∂(pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)),
        0 ≤ p.1 ∧ 0 ≤ p.2 := by
      filter_upwards [ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2)] with p hp
      exact ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, (pairedEtaLogSupport_subset_Ioi_zero hp.2).le⟩
    apply (normalized_integral_current_gapReturn_tendsto
      (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N) measurable_fst hpos ha).congr'
    filter_upwards [heq] with h hh
    simp only [pairedEtaLeadingCurrentNormalizedGapReturn, hh, if_neg hm]

/-- Positive endpoint damping preserves genuine integrability of a current. -/
theorem integrable_current_endpointTilt {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p : ℝ × ℝ ↦ (f p : ℂ) * (Real.exp (-a * (T p + p.2) / 2) : ℂ)) μ := by
  apply hf.ofReal.mul_bdd (by fun_prop)
  filter_upwards [hpos] with p hp
  change ‖(Real.exp (-a * (T p + p.2) / 2) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha (add_nonneg hp.1 hp.2)])

/-- Removing positive endpoint damping recovers the actual current integral. -/
theorem integral_current_endpointTilt_tendsto {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) :
    Tendsto (fun a : ℝ ↦ ∫ p : ℝ × ℝ, (f p : ℂ) *
      (Real.exp (-a * (T p + p.2) / 2) : ℂ) ∂μ) (𝓝[>] 0)
      (𝓝 ((∫ p : ℝ × ℝ, f p ∂μ : ℝ) : ℂ)) := by
  rw [← integral_complex_ofReal]
  apply tendsto_integral_filter_of_dominated_convergence (fun p ↦ |f p|)
  · apply Eventually.of_forall
    intro a
    exact hf.ofReal.aestronglyMeasurable.mul
      (show Measurable (fun p : ℝ × ℝ ↦ (Real.exp (-a * (T p + p.2) / 2) : ℂ)) by fun_prop).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    filter_upwards [hpos] with p hp
    have he : Real.exp (-a * (T p + p.2) / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha.le (add_nonneg hp.1 hp.2)])
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) he
  · exact hf.abs
  · apply Eventually.of_forall
    intro p
    have hc : Continuous (fun a : ℝ ↦ (f p : ℂ) * (Real.exp (-a * (T p + p.2) / 2) : ℂ)) := by fun_prop
    simpa only [neg_zero, zero_mul, zero_div, Real.exp_zero, Complex.ofReal_one, mul_one] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Removing the endpoint tilt reconstructs the original isolated leading
flux, including its distinct multiplicity-one head contribution. -/
theorem pairedEtaLeadingCurrentTiltedIntegral_tendsto (rho : NontrivialZetaZero) (N : ℕ) :
    Tendsto (pairedEtaLeadingCurrentTiltedIntegral rho N) (𝓝[>] 0)
      (𝓝 (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)) := by
  unfold pairedEtaLeadingCurrentTiltedIntegral
  split_ifs with hm
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_headKernel_of_multiplicity_eq_one rho hm N]
    apply integral_current_endpointTilt_tendsto (integrable_topPrefixFiniteEnergyHeadKernel rho N)
      (measurable_fst.add_const _)
    filter_upwards [ae_pair_mem_pairedEtaLogSupport_headMeasure N] with p hp
    exact ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, (pairedEtaLogSupport_subset_Ioi_zero hp.2).le⟩
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_factoredAdjacentMomentKernel_of_two_le_multiplicity rho
      (show 2 ≤ analyticZetaZeroMultiplicity rho by have := analyticZetaZeroMultiplicity_positive rho; omega) N]
    apply integral_current_endpointTilt_tendsto (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      measurable_fst
    filter_upwards [ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2)] with p hp
    exact ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, (pairedEtaLogSupport_subset_Ioi_zero hp.2).le⟩

/-- Exact iterated reconstruction from the full actual gap return: first
broaden the heat at each positive tilt, then remove that tilt. The arithmetic
cutoff and actual zero remain fixed in these two proved limits. -/
theorem pairedEtaLeadingCurrent_gapReturn_reconstruction (rho : NontrivialZetaZero) (N : ℕ) :
    (∀ a : ℝ, 0 < a →
      Tendsto (pairedEtaLeadingCurrentNormalizedGapReturn rho N a) atTop
        (𝓝 (pairedEtaLeadingCurrentTiltedIntegral rho N a))) ∧
    Tendsto (pairedEtaLeadingCurrentTiltedIntegral rho N) (𝓝[>] 0)
      (𝓝 (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)) :=
  ⟨fun _ ha ↦ pairedEtaLeadingCurrentNormalizedGapReturn_tendsto rho N ha,
    pairedEtaLeadingCurrentTiltedIntegral_tendsto rho N⟩

end

end RiemannGaussian
