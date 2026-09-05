import RiemannGaussian.EtaSupportGapGaussian
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramLocalized

/-!
# The actual support/gap cross integral behind eta heat transfer

The positive half-line splits into the literal eta support and its omitted
intervals. A symmetric kernel which vanishes within either colour is twice
its support-to-gap integral. This gives the precise spatial normalization
needed for the Gaussian spectral identity.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The literal gap measure is s-finite as a restriction of Lebesgue measure. -/
instance pairedEtaLogGapMeasure.instSFinite : SFinite pairedEtaLogGapMeasure := by
  unfold pairedEtaLogGapMeasure
  infer_instance

/-- Almost every pair for a product of restricted Lebesgue measures belongs
to the corresponding product set. -/
theorem ae_mem_product_restrict {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∀ᵐ p : ℝ × ℝ ∂((volume.restrict A).prod (volume.restrict B)), p ∈ A ×ˢ B := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (hA.prod hB)

/-- Positive-quadrant integration splits into the two actual eta colours,
with the two same-colour kernels zero and the two ordered cross terms equal. -/
theorem integral_positiveQuadrant_eq_twice_support_gap {F : ℝ × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
    (hsymm : ∀ t u : ℝ, F (t, u) = F (u, t))
    (hAA : ∀ t ∈ pairedEtaLogSupport, ∀ u ∈ pairedEtaLogSupport, F (t, u) = 0)
    (hGG : ∀ t ∈ pairedEtaLogGapSupport, ∀ u ∈ pairedEtaLogGapSupport, F (t, u) = 0) :
    (∫ p, F p ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      2 * ∫ p, F p ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
  have hsplit : (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) =
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure + pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) +
      (pairedEtaLogGapMeasure.prod pairedEtaLogMeasure + pairedEtaLogGapMeasure.prod pairedEtaLogGapMeasure) := by
    rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure,
      Measure.add_prod, Measure.prod_add, Measure.prod_add]
  rw [hsplit] at hF ⊢
  obtain ⟨hiA, hiG⟩ := integrable_add_measure.mp hF
  obtain ⟨hiAA, hiAG⟩ := integrable_add_measure.mp hiA
  obtain ⟨hiGA, hiGG⟩ := integrable_add_measure.mp hiG
  have hzeroAA : (∫ p, F p ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_mem_product_restrict measurableSet_pairedEtaLogSupport
      measurableSet_pairedEtaLogSupport] with p hp
    exact hAA p.1 hp.1 p.2 hp.2
  have hzeroGG : (∫ p, F p ∂(pairedEtaLogGapMeasure.prod pairedEtaLogGapMeasure)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_mem_product_restrict measurableSet_pairedEtaLogGapSupport
      measurableSet_pairedEtaLogGapSupport] with p hp
    exact hGG p.1 hp.1 p.2 hp.2
  have hswap : (∫ p, F p ∂(pairedEtaLogGapMeasure.prod pairedEtaLogMeasure)) =
      ∫ p, F p ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
    rw [← integral_prod_swap F]
    apply integral_congr_ae
    exact Eventually.of_forall fun p ↦ hsymm p.2 p.1
  rw [integral_add_measure hiA hiG, integral_add_measure hiAA hiAG,
    integral_add_measure hiGA hiGG, hzeroAA, hzeroGG, hswap]
  ring

/-- The actual support/gap heat transfer is twice its one-way cross integral. -/
theorem pairedEtaSupportGapGaussianLeakage_eq_twice_cross {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi : ℝ → ℝ} (hphi : Measurable phi) :
    pairedEtaSupportGapGaussianLeakage sigma h phi =
      2 * ∫ p, pairedEtaSupportGapHeatKernel sigma h phi p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
  apply integral_positiveQuadrant_eq_twice_support_gap
    (integrable_pairedEtaSupportGapHeatKernel hsigma hh hphi)
    (pairedEtaSupportGapHeatKernel_swap sigma h phi)
  · intro t ht u hu
    simp [pairedEtaSupportGapHeatKernel, pairedEtaSupportGapHeatWeight,
      pairedEtaLogShiftMismatch_sub, pairedEtaLogIndicator, ht, hu]
  · intro t ht u hu
    have ht' : t ∉ pairedEtaLogSupport := ht.2
    have hu' : u ∉ pairedEtaLogSupport := hu.2
    simp [pairedEtaSupportGapHeatKernel, pairedEtaSupportGapHeatWeight,
      pairedEtaLogShiftMismatch_sub, pairedEtaLogIndicator, ht', hu']

/-- On the ordered support/gap product, the mismatch is exactly one and
the continuous heat kernel has its literal Gaussian normalization. -/
theorem pairedEtaSupportGapHeatKernel_eq_localized_cross {sigma h gamma t u : ℝ}
    (hh : 0 < h) (ht : t ∈ pairedEtaLogSupport) (hu : u ∈ pairedEtaLogGapSupport) :
    pairedEtaSupportGapHeatKernel sigma h (fun t ↦ gamma * t) (t, u) =
      (1 / (2 * Real.sqrt Real.pi * h)) *
        pairedEtaLocalizedGaussianLaplaceKernel sigma (h ^ 2) gamma (t, u) := by
  have hu' : u ∉ pairedEtaLogSupport := hu.2
  simp only [pairedEtaSupportGapHeatKernel, pairedEtaSupportGapHeatWeight,
    pairedEtaLogShiftMismatch_sub, pairedEtaLogIndicator, Set.indicator_of_mem ht,
    Set.indicator_of_notMem hu']
  norm_num only [sub_self, zero_sub, neg_sq, one_pow, mul_one]
  unfold etaNormalizedHeatKernel pairedEtaLocalizedGaussianLaplaceKernel
    pairedEtaFiniteGaussianLaplaceKernel
  have hquad : -(1 / 4) * ((u - t) / h) ^ 2 = -(t - u) ^ 2 / (4 * h ^ 2) := by
    field_simp
    ring
  rw [hquad, show gamma * u - gamma * t = gamma * (u - t) by ring]
  ring

/-- The continuous eta heat transfer is the normalized localized cross
integral of the actual support and gap measures. -/
theorem pairedEtaSupportGapGaussianLeakage_linear_eq_localized_cross {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (gamma : ℝ) :
    pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ gamma * t) =
      (1 / (Real.sqrt Real.pi * h)) *
        ∫ p, pairedEtaLocalizedGaussianLaplaceKernel sigma (h ^ 2) gamma p
          ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
  have hphi : Measurable (fun t : ℝ ↦ gamma * t) := measurable_const.mul measurable_id
  rw [pairedEtaSupportGapGaussianLeakage_eq_twice_cross hsigma hh hphi]
  have hcross : (∫ p, pairedEtaSupportGapHeatKernel sigma h (fun t ↦ gamma * t) p
      ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure)) =
      (1 / (2 * Real.sqrt Real.pi * h)) *
        ∫ p, pairedEtaLocalizedGaussianLaplaceKernel sigma (h ^ 2) gamma p
          ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_mem_product_restrict measurableSet_pairedEtaLogSupport
      measurableSet_pairedEtaLogGapSupport] with p hp
    exact pairedEtaSupportGapHeatKernel_eq_localized_cross hh hp.1 hp.2
  rw [hcross]
  ring

end

end RiemannGaussian
