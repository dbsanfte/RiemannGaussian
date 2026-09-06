import RiemannGaussian.EtaGapReturnMultiplier

/-!
# Quantitative reconstruction error on the literal completed current

Fubini retains the exact normalized multiplier inside the original signed
current. The error before taking a norm is another current integral. A
uniform finite-support estimate then keeps the physical endpoint, heat
width, tilt, and actual completed-current absolute mass explicit.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual gap multiplier is measurable jointly in its endpoint times. -/
theorem measurable_pairedEtaGapReturnMultiplier (a h : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ pairedEtaGapReturnMultiplier a h p.1 p.2) := by
  have hm : Measurable (fun z : (ℝ × ℝ) × ℝ ↦ Real.exp (-a * z.2) *
      (pairedEtaHeatTransitionProfile h (z.2 - z.1.1) * pairedEtaHeatTransitionProfile h (z.1.2 - z.2))) := by
    unfold pairedEtaHeatTransitionProfile
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.div_const _

/-- The exact endpoint damping and gap return together approach one with
both scale errors and the finite physical endpoint retained. -/
theorem endpointTilt_gapReturnMultiplier_error_le {a h L t u : ℝ}
    (ha : 0 < a) (hh : 0 < h) (ht : t ∈ Icc 0 L) (hu : u ∈ Icc 0 L) :
    |Real.exp (-a * (t + u) / 2) * pairedEtaGapReturnMultiplier a h t u - 1| ≤
      a * L + (pairedEtaGapLaplaceSecondMoment a / pairedEtaGapLaplaceMass a + 2 * L ^ 2) / h ^ 2 := by
  have hepos := (Real.exp_pos (-a * (t + u) / 2)).le
  have he : Real.exp (-a * (t + u) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1, hu.1])
  have htilt : |Real.exp (-a * (t + u) / 2) - 1| ≤ a * L := by
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    have hx := Real.add_one_le_exp (-a * (t + u) / 2)
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add ht.2 hu.2) ha.le]
  have hgap : |pairedEtaGapReturnMultiplier a h t u - 1| ≤
      (pairedEtaGapLaplaceSecondMoment a / pairedEtaGapLaplaceMass a + 2 * L ^ 2) / h ^ 2 := by
    apply (pairedEtaGapReturnMultiplier_error_le ha hh t u).trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg h)
    have ht2 := mul_self_le_mul_self ht.1 ht.2
    have hu2 := mul_self_le_mul_self hu.1 hu.2
    nlinarith
  calc
    _ = |Real.exp (-a * (t + u) / 2) * (pairedEtaGapReturnMultiplier a h t u - 1) +
        (Real.exp (-a * (t + u) / 2) - 1)| := by congr 1; ring
    _ ≤ |Real.exp (-a * (t + u) / 2) * (pairedEtaGapReturnMultiplier a h t u - 1)| +
        |Real.exp (-a * (t + u) / 2) - 1| := abs_add_le _ _
    _ ≤ |pairedEtaGapReturnMultiplier a h t u - 1| + a * L := by
      rw [abs_mul, abs_of_nonneg hepos]
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) he) htilt
    _ ≤ _ := by linarith

/-- The actual current times the endpoint-damped multiplier is integrable. -/
theorem integrable_current_endpointTilt_gapMultiplier {μ : Measure (ℝ × ℝ)}
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a : ℝ} (ha : 0 < a) (h : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ (f p : ℂ) *
      (Real.exp (-a * (T p + p.2) / 2) * pairedEtaGapReturnMultiplier a h (T p) p.2 : ℝ)) μ := by
  have hm := ((measurable_pairedEtaGapReturnMultiplier a h).comp (hT.prodMk measurable_snd)).complex_ofReal
  have hi := (integrable_current_endpointTilt hf hT hpos ha.le).mul_bdd hm.aestronglyMeasurable
    (Eventually.of_forall fun p ↦ show ‖(pairedEtaGapReturnMultiplier a h (T p) p.2 : ℂ)‖ ≤ 1 from by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pairedEtaGapReturnMultiplier_bounds ha h (T p) p.2).1]
      exact (pairedEtaGapReturnMultiplier_bounds ha h (T p) p.2).2)
  simpa only [Complex.ofReal_mul, mul_assoc, Function.comp_def] using hi

/-- Fubini preserves the exact return multiplier inside the completed
current, including its sign and ordinate phase. -/
theorem normalized_current_gapReturn_eq_multiplier {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    (((pairedEtaHeatTransitionAmplitude h) ^ 2 / pairedEtaGapLaplaceMass a : ℝ) : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂(μ.prod pairedEtaLogGapMeasure)) =
      ∫ p : ℝ × ℝ, (f p : ℂ) *
        (Real.exp (-a * (T p + p.2) / 2) * pairedEtaGapReturnMultiplier a h (T p) p.2 : ℝ) ∂μ := by
  have hraw := integrable_current_gapReturn_prod hf hT hpos ha.le hh ha.le hh (by linarith)
    (phi := fun _ ↦ 0) (psi := fun _ ↦ 0) measurable_const measurable_const
  have hbro : Integrable (fun z : (ℝ × ℝ) × ℝ ↦ (f z.1 : ℂ) *
      (pairedEtaBroadGapReturnKernel a h (T z.1) z.1.2 z.2 : ℂ)) (μ.prod pairedEtaLogGapMeasure) := by
    apply (hraw.const_mul (((pairedEtaHeatTransitionAmplitude h) ^ 2 : ℝ) : ℂ)).congr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae ae_mem_pairedEtaLogGapSupport] with z hz
    rw [pairedEtaBroadGapReturnKernel_eq_scaled hh a (T z.1) z.1.2 hz]
    ring
  calc
    _ = (pairedEtaGapLaplaceMass a : ℂ)⁻¹ *
        ∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
          (pairedEtaBroadGapReturnKernel a h (T z.1) z.1.2 z.2 : ℂ) ∂(μ.prod pairedEtaLogGapMeasure) := by
      rw [integral_current_broadGapReturn_eq_scaled f T hh a]
      push_cast
      ring
    _ = _ := by
      rw [integral_prod _ hbro, ← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro p
      dsimp only
      have heq : (fun w : ℝ ↦ (f p : ℂ) * (pairedEtaBroadGapReturnKernel a h (T p) p.2 w : ℂ)) =
          (fun w ↦ ((f p : ℂ) * (Real.exp (-a * (T p + p.2) / 2) : ℂ)) *
            (Real.exp (-a * w) * (pairedEtaHeatTransitionProfile h (w - T p) *
              pairedEtaHeatTransitionProfile h (p.2 - w)) : ℝ)) := by
        ext w
        unfold pairedEtaBroadGapReturnKernel
        push_cast
        ring
      rw [heq, integral_const_mul, integral_complex_ofReal]
      unfold pairedEtaGapReturnMultiplier
      push_cast
      ring

/-- The exact signed reconstruction error is a current integral before
any absolute value or norm is applied. -/
theorem normalized_current_gapReturn_sub_integral {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    (((pairedEtaHeatTransitionAmplitude h) ^ 2 / pairedEtaGapLaplaceMass a : ℝ) : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂(μ.prod pairedEtaLogGapMeasure)) - ((∫ p, f p ∂μ : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, (f p : ℂ) *
        (Real.exp (-a * (T p + p.2) / 2) * pairedEtaGapReturnMultiplier a h (T p) p.2 - 1 : ℝ) ∂μ := by
  rw [normalized_current_gapReturn_eq_multiplier hf hT hpos ha hh, ← integral_complex_ofReal]
  calc
    _ = ∫ p : ℝ × ℝ, (f p : ℂ) *
        (Real.exp (-a * (T p + p.2) / 2) * pairedEtaGapReturnMultiplier a h (T p) p.2 : ℝ) - (f p : ℂ) ∂μ :=
      (integral_sub (integrable_current_endpointTilt_gapMultiplier hf hT hpos ha h) hf.ofReal).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro p
      simp only [Complex.ofReal_sub, Complex.ofReal_one]
      ring

/-- The reconstruction error is uniform on a finite physical time window,
with the actual absolute current mass and both scale costs explicit. -/
theorem norm_normalized_current_gapReturn_sub_integral_le {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T) {L : ℝ}
    (hwindow : ∀ᵐ p ∂μ, T p ∈ Icc 0 L ∧ p.2 ∈ Icc 0 L) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    ‖(((pairedEtaHeatTransitionAmplitude h) ^ 2 / pairedEtaGapLaplaceMass a : ℝ) : ℂ) *
      (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂(μ.prod pairedEtaLogGapMeasure)) - ((∫ p, f p ∂μ : ℝ) : ℂ)‖ ≤
      (∫ p, |f p| ∂μ) *
        (a * L + (pairedEtaGapLaplaceSecondMoment a / pairedEtaGapLaplaceMass a + 2 * L ^ 2) / h ^ 2) := by
  have hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2 := hwindow.mono fun _ hp ↦ ⟨hp.1.1, hp.2.1⟩
  rw [normalized_current_gapReturn_sub_integral hf hT hpos ha hh, ← integral_mul_const]
  apply norm_integral_le_of_norm_le (hf.abs.mul_const _)
  filter_upwards [hwindow] with p hp
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (endpointTilt_gapReturnMultiplier_error_le ha hh hp.1 hp.2) (abs_nonneg _)

/-- The two physical head-current times lie in the actual successor-prefix
window, including the restored first coordinate. -/
theorem ae_head_current_physical_window (N : ℕ) :
    ∀ᵐ p : ℝ × ℝ ∂(pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)),
      p.1 + pairedEtaLogTailCutoff (N + 1) ∈ Icc 0 (pairedEtaLogTailCutoff (N + 2)) ∧
      p.2 ∈ Icc 0 (pairedEtaLogTailCutoff (N + 2)) := by
  have hhead : ∀ᵐ t : ℝ ∂pairedEtaShiftedLogHeadMeasure (N + 1),
      t + pairedEtaLogTailCutoff (N + 1) ≤ pairedEtaLogTailCutoff (N + 2) := by
    rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hw := pairedEtaShiftedLogHeadWidth_lt_shiftIncrement (N + 1)
    unfold pairedEtaLogTailShiftIncrement at hw
    have htupper := ht.2
    linarith
  filter_upwards [ae_pair_mem_pairedEtaLogSupport_headMeasure N,
    Measure.quasiMeasurePreserving_fst.ae hhead,
    Measure.quasiMeasurePreserving_snd.ae (ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure (N + 2))]
    with p hp ht hu
  exact ⟨⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, ht⟩,
    ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.2).le, hu.le⟩⟩

/-- Both adjacent-current coordinates lie in the literal successor-prefix window. -/
theorem ae_adjacent_current_physical_window (N : ℕ) :
    ∀ᵐ p : ℝ × ℝ ∂(pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)),
      p.1 ∈ Icc 0 (pairedEtaLogTailCutoff (N + 2)) ∧ p.2 ∈ Icc 0 (pairedEtaLogTailCutoff (N + 2)) := by
  filter_upwards [ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2),
    Measure.quasiMeasurePreserving_fst.ae (ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure (N + 2)),
    Measure.quasiMeasurePreserving_snd.ae (ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure (N + 2))]
    with p hp ht hu
  exact ⟨⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, ht.le⟩,
    ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.2).le, hu.le⟩⟩

/-- The genuine finite absolute mass of the multiplicity-selected completed
kernel. This quantity is used only to bound the reconstruction error. -/
def pairedEtaLeadingCurrentAbsoluteKernelMass (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ p : ℝ × ℝ, |pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p|
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ p : ℝ × ℝ, |pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p|
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))

/-- The actual absolute kernel mass is nonnegative in either multiplicity branch. -/
theorem pairedEtaLeadingCurrentAbsoluteKernelMass_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaLeadingCurrentAbsoluteKernelMass rho N := by
  unfold pairedEtaLeadingCurrentAbsoluteKernelMass
  split <;> exact integral_nonneg fun _ ↦ abs_nonneg _

/-- Quantitative reconstruction of the original leading flux on its actual
carrier. The cutoff endpoint, completed absolute mass, positive tilt, and
heat width are retained, with no weighted-series interchange. -/
theorem pairedEtaLeadingCurrentNormalizedGapReturn_error_le (rho : NontrivialZetaZero) (N : ℕ)
    {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    ‖pairedEtaLeadingCurrentNormalizedGapReturn rho N a h -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      pairedEtaLeadingCurrentAbsoluteKernelMass rho N *
        (a * pairedEtaLogTailCutoff (N + 2) +
          (pairedEtaGapLaplaceSecondMoment a / pairedEtaGapLaplaceMass a +
            2 * pairedEtaLogTailCutoff (N + 2) ^ 2) / h ^ 2) := by
  unfold pairedEtaLeadingCurrentNormalizedGapReturn
  rw [pairedEtaLeadingCurrentIntegratedGapReturn_eq_prod rho N ha.le hh ha.le hh
    (by linarith) measurable_const measurable_const]
  unfold pairedEtaLeadingCurrentAbsoluteKernelMass
  split_ifs with hm
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_headKernel_of_multiplicity_eq_one rho hm N]
    exact norm_normalized_current_gapReturn_sub_integral_le (integrable_topPrefixFiniteEnergyHeadKernel rho N)
      (measurable_fst.add_const _) (ae_head_current_physical_window N) ha hh
  · rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_factoredAdjacentMomentKernel_of_two_le_multiplicity rho
      (show 2 ≤ analyticZetaZeroMultiplicity rho by have := analyticZetaZeroMultiplicity_positive rho; omega) N]
    exact norm_normalized_current_gapReturn_sub_integral_le (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      measurable_fst (ae_adjacent_current_physical_window N) ha hh

/-- One fixed positive gap mass yields a reconstruction estimate valid
uniformly for `0 < a ≤ 1`, with its full cubic tilt cost displayed. -/
theorem pairedEtaLeadingCurrentNormalizedGapReturn_error_le_smallTilt (rho : NontrivialZetaZero) (N : ℕ)
    {a h : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 < h) :
    ‖pairedEtaLeadingCurrentNormalizedGapReturn rho N a h -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      pairedEtaLeadingCurrentAbsoluteKernelMass rho N *
        (a * pairedEtaLogTailCutoff (N + 2) +
          (2 / (pairedEtaGapLaplaceMass 1 * a ^ 3) +
            2 * pairedEtaLogTailCutoff (N + 2) ^ 2) / h ^ 2) := by
  apply (pairedEtaLeadingCurrentNormalizedGapReturn_error_le rho N ha hh).trans
  apply mul_le_mul_of_nonneg_left _ (pairedEtaLeadingCurrentAbsoluteKernelMass_nonneg rho N)
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  exact add_le_add (pairedEtaGapLaplaceSecondMoment_div_mass_le ha ha1) le_rfl

end

end RiemannGaussian
