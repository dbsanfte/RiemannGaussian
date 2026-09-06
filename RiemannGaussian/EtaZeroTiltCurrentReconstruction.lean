import RiemannGaussian.EtaZeroTiltGapMultiplier

/-!
# Quantitative zero-tilt reconstruction of the original completed current

The actual full-gap return receives its Gaussian mass normalization.
Fubini retains its exact signed multiplier on both multiplicity carriers;
the finite physical window then gives an explicit inverse-width error.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The unchanged integrated return with the proved zero-tilt normalization. -/
def pairedEtaLeadingCurrentZeroTiltGapReturn (rho : NontrivialZetaZero) (N : ℕ) (h : ℝ) : ℂ :=
  (pairedEtaZeroTiltGapNormalization h : ℂ) *
    pairedEtaLeadingCurrentIntegratedGapReturn rho N 0 h 0 h (fun _ ↦ 0) (fun _ ↦ 0)

/-- Multiplying an integrable current by the actual zero-tilt multiplier
preserves genuine integrability. -/
theorem integrable_current_zeroTiltGapMultiplier {μ : Measure (ℝ × ℝ)}
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    {h : ℝ} (hh : 2 ≤ h) :
    Integrable (fun p ↦ (f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 : ℂ)) μ := by
  have hm := ((measurable_pairedEtaZeroTiltGapMultiplier h).comp (hT.prodMk measurable_snd)).complex_ofReal
  exact hf.ofReal.mul_bdd hm.aestronglyMeasurable (Eventually.of_forall fun p ↦ by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairedEtaZeroTiltGapMultiplier_bounds hh (T p) p.2).1]
    exact (pairedEtaZeroTiltGapMultiplier_bounds hh (T p) p.2).2)

/-- The actual normalized three-time gap integral retains the exact
zero-tilt multiplier inside the signed current integral. -/
theorem normalized_current_zeroTiltGapReturn_eq_multiplier {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {h : ℝ} (hh : 0 < h) :
    (pairedEtaZeroTiltGapNormalization h : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂μ.prod pairedEtaLogGapMeasure) =
      ∫ p, (f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 : ℂ) ∂μ := by
  have hi := Integrable.mono_measure
    (integrable_current_fullTwoHeat_prod hf hT hpos (by norm_num : (0 : ℝ) ≤ 0) hh
      (phi := fun _ ↦ 0) (psi := fun _ ↦ 0) measurable_const measurable_const)
    (Measure.prod_mono le_rfl (show pairedEtaLogGapMeasure ≤ volume from Measure.restrict_le_self))
  rw [integral_prod _ hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  rw [integral_const_mul]
  calc
    _ = (f p : ℂ) * ((pairedEtaZeroTiltGapNormalization h : ℂ) *
        ∫ w, pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) (T p) p.2 w
          ∂pairedEtaLogGapMeasure) := by ring
    _ = _ := by rw [integral_fullTwoHeat_zero_phase_gap_normalized hh]

/-- The exact signed reconstruction defect is retained before applying a norm. -/
theorem normalized_current_zeroTiltGapReturn_sub_integral {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {h : ℝ} (hh : 2 ≤ h) :
    (pairedEtaZeroTiltGapNormalization h : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂μ.prod pairedEtaLogGapMeasure) - ((∫ p, f p ∂μ : ℝ) : ℂ) =
      ∫ p, (f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 - 1 : ℝ) ∂μ := by
  rw [normalized_current_zeroTiltGapReturn_eq_multiplier hf hT hpos (by linarith), ← integral_complex_ofReal]
  calc
    _ = ∫ p, (f p : ℂ) * (pairedEtaZeroTiltGapMultiplier h (T p) p.2 : ℂ) - (f p : ℂ) ∂μ :=
      (integral_sub (integrable_current_zeroTiltGapMultiplier hf hT hh) hf.ofReal).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      push_cast
      ring

/-- The uniform physical-window bound applies to the original integrable
current without replacing its sign or ordinate phase. -/
theorem norm_normalized_current_zeroTiltGapReturn_sub_integral_le
    {μ : Measure (ℝ × ℝ)} [SFinite μ] {f : ℝ × ℝ → ℝ} (hf : Integrable f μ)
    {T : ℝ × ℝ → ℝ} (hT : Measurable T) {L : ℝ}
    (hwindow : ∀ᵐ p ∂μ, T p ∈ Icc 0 L ∧ p.2 ∈ Icc 0 L) {h : ℝ} (hh : 2 ≤ h) :
    ‖(pairedEtaZeroTiltGapNormalization h : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂μ.prod pairedEtaLogGapMeasure) - ((∫ p, f p ∂μ : ℝ) : ℂ)‖ ≤
      (∫ p, |f p| ∂μ) * (13 * (1 + L) ^ 2 / h) := by
  have hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2 := hwindow.mono fun _ hp ↦ ⟨hp.1.1, hp.2.1⟩
  rw [normalized_current_zeroTiltGapReturn_sub_integral hf hT hpos hh, ← integral_mul_const]
  apply norm_integral_le_of_norm_le (hf.abs.mul_const _)
  filter_upwards [hwindow] with p hp
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pairedEtaZeroTiltGapMultiplier_window_error_le hh hp.1 hp.2) (abs_nonneg _)

/-- Both actual multiplicity branches satisfy the same zero-tilt error
bound, including the restored physical head coordinate. -/
theorem pairedEtaLeadingCurrentZeroTiltGapReturn_error_le (rho : NontrivialZetaZero) (N : ℕ)
    {h : ℝ} (hh : 2 ≤ h) :
    ‖pairedEtaLeadingCurrentZeroTiltGapReturn rho N h -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      pairedEtaLeadingCurrentAbsoluteKernelMass rho N *
        (13 * (1 + pairedEtaLogTailCutoff (N + 2)) ^ 2 / h) := by
  unfold pairedEtaLeadingCurrentZeroTiltGapReturn
  rw [(pairedEtaLeadingCurrentIntegratedGapReturn_fullHeat rho N (by norm_num : (0 : ℝ) ≤ 0)
    (by linarith : 0 < h) (phi := fun _ ↦ 0) (psi := fun _ ↦ 0) measurable_const measurable_const).2]
  unfold pairedEtaLeadingCurrentFullTwoHeatIntegral pairedEtaLeadingCurrentAbsoluteKernelMass
  split_ifs with hm
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_headKernel_of_multiplicity_eq_one rho hm N]
    exact norm_normalized_current_zeroTiltGapReturn_sub_integral_le
      (integrable_topPrefixFiniteEnergyHeadKernel rho N) (measurable_fst.add_const _)
      (ae_head_current_physical_window N) hh
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_factoredAdjacentMomentKernel_of_two_le_multiplicity rho
      (show 2 ≤ analyticZetaZeroMultiplicity rho by have := analyticZetaZeroMultiplicity_positive rho; omega) N]
    exact norm_normalized_current_zeroTiltGapReturn_sub_integral_le
      (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N) measurable_fst
      (ae_adjacent_current_physical_window N) hh

end

end RiemannGaussian
