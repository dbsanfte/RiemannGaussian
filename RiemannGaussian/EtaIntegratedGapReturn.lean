import RiemannGaussian.EtaCompletedGapReturnPairing
import RiemannGaussian.EtaSupportGapGaussianSpectral

/-!
# Integration of the completed current through the entire eta gap

The intermediate time is integrated over the literal infinite gap measure.
Positive total tilt supplies an exponential majorant for the two ordered
heat transitions, while the original current supplies the other integrable
factor. Both Fubini orders retain the complex phases, completion factors,
multiplicity, cutoff, and translated head coordinate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The Gaussian amplitude denominator for one actual heat commutator. -/
def pairedEtaHeatTransitionAmplitude (h : ℝ) : ℝ :=
  2 * Real.sqrt Real.pi * (Real.sqrt 2 * h)

/-- The transition amplitude denominator is strictly positive at positive width. -/
theorem pairedEtaHeatTransitionAmplitude_pos {h : ℝ} (hh : 0 < h) :
    0 < pairedEtaHeatTransitionAmplitude h := by
  unfold pairedEtaHeatTransitionAmplitude
  positivity

/-- Almost every intermediate time belongs to the actual positive gap. -/
theorem ae_mem_pairedEtaLogGapSupport :
    ∀ᵐ w : ℝ ∂pairedEtaLogGapMeasure, w ∈ pairedEtaLogGapSupport :=
  ae_restrict_mem measurableSet_pairedEtaLogGapSupport

/-- The restored head measure is finite because it is one bounded interval. -/
instance pairedEtaShiftedLogHeadMeasure.instIsFiniteMeasure (N : ℕ) :
    IsFiniteMeasure (pairedEtaShiftedLogHeadMeasure N) := by
  rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
  infer_instance

/-- Joint measurability of the full ordered return kernel, before taking a norm. -/
theorem measurable_pairedEtaOrderedGapReturnKernelCore {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) (sigma h tau k : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × ℝ ↦
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi z.1.1 z.1.2 z.2) := by
  have hchi := measurable_pairedEtaLogIndicator.comp (measurable_snd : Measurable (Prod.snd : (ℝ × ℝ) × ℝ → ℝ))
  have hp : Measurable (fun z : (ℝ × ℝ) × ℝ ↦ pairedEtaHeatPhaseUnit phi (z.2, z.1.1)) :=
    (measurable_pairedEtaHeatPhaseUnit hphi).comp
      (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
  have hq : Measurable (fun z : (ℝ × ℝ) × ℝ ↦ pairedEtaHeatPhaseUnit psi (z.1.2, z.2)) :=
    (measurable_pairedEtaHeatPhaseUnit hpsi).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hb : Measurable (fun z : (ℝ × ℝ) × ℝ ↦
    Real.exp (-sigma * (z.1.1 + z.2) / 2) *
      (Real.exp (-(1 / 4) * ((z.2 - z.1.1) / (Real.sqrt 2 * h)) ^ 2) /
        (2 * Real.sqrt Real.pi * (Real.sqrt 2 * h))) *
      Real.exp (-tau * (z.2 + z.1.2) / 2) *
      (Real.exp (-(1 / 4) * ((z.1.2 - z.2) / (Real.sqrt 2 * k)) ^ 2) /
        (2 * Real.sqrt Real.pi * (Real.sqrt 2 * k)))) := by fun_prop
  exact ((hb.mul (measurable_const.sub hchi)).complex_ofReal.mul hp).mul hq

/-- The ordered return retains exponential decay in the intermediate time.
This estimate is independent of both real phases. -/
theorem norm_pairedEtaOrderedGapReturnKernelCore_le {sigma h tau k t u : ℝ}
    (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (phi psi : ℝ → ℝ) (w : ℝ) :
    ‖pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi t u w‖ ≤
      (pairedEtaHeatTransitionAmplitude h * pairedEtaHeatTransitionAmplitude k)⁻¹ *
        Real.exp (-((sigma + tau) / 2) * w) := by
  have hgap : |1 - pairedEtaLogIndicator w| ≤ 1 := by
    rcases pairedEtaLogIndicator_eq_zero_or_one w with hw | hw <;> simp [hw]
  have hh' : 0 < Real.sqrt 2 * h := by positivity
  have hk' : 0 < Real.sqrt 2 * k := by positivity
  have hph := (etaNormalizedHeatKernel_pos hh' (w - t)).le
  have hpk := (etaNormalizedHeatKernel_pos hk' (u - w)).le
  have hexp : Real.exp (-sigma * (t + w) / 2) * Real.exp (-tau * (w + u) / 2) ≤
      Real.exp (-((sigma + tau) / 2) * w) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_nonneg hsigma ht, mul_nonneg htau hu]
  have hheat : etaNormalizedHeatKernel (Real.sqrt 2 * h) (w - t) *
      etaNormalizedHeatKernel (Real.sqrt 2 * k) (u - w) ≤
      (pairedEtaHeatTransitionAmplitude h * pairedEtaHeatTransitionAmplitude k)⁻¹ := by
    simpa only [pairedEtaHeatTransitionAmplitude, one_div, mul_inv] using
      mul_le_mul (etaNormalizedHeatKernel_le hh' (w - t))
        (etaNormalizedHeatKernel_le hk' (u - w))
        (etaNormalizedHeatKernel_pos hk' _).le (by positivity)
  simp only [pairedEtaOrderedGapReturnKernelCore, norm_mul, norm_pairedEtaHeatPhaseUnit,
    mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (etaNormalizedHeatKernel_pos hh' _),
    abs_of_pos (etaNormalizedHeatKernel_pos hk' _)]
  calc
    _ ≤ Real.exp (-sigma * (t + w) / 2) * etaNormalizedHeatKernel (Real.sqrt 2 * h) (w - t) *
        Real.exp (-tau * (w + u) / 2) * etaNormalizedHeatKernel (Real.sqrt 2 * k) (u - w) * 1 :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = (Real.exp (-sigma * (t + w) / 2) * Real.exp (-tau * (w + u) / 2)) *
        (etaNormalizedHeatKernel (Real.sqrt 2 * h) (w - t) *
          etaNormalizedHeatKernel (Real.sqrt 2 * k) (u - w)) := by ring
    _ ≤ Real.exp (-((sigma + tau) / 2) * w) *
        (pairedEtaHeatTransitionAmplitude h * pairedEtaHeatTransitionAmplitude k)⁻¹ :=
      mul_le_mul hexp hheat (by positivity) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- An integrable current with positive physical endpoints has a genuinely
integrable three-time return kernel at positive total tilt. -/
theorem integrable_current_gapReturn_prod {μ : Measure (ℝ × ℝ)}
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {sigma h tau k : ℝ}
    (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k)
    (hst : 0 < sigma + tau) {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦ (f z.1 : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi (T z.1) z.1.2 z.2)
      (μ.prod pairedEtaLogGapMeasure) := by
  have hm := (measurable_pairedEtaOrderedGapReturnKernelCore hphi hpsi sigma h tau k).comp
    (((hT.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have he := integrable_rexp_neg_mul_pairedEtaLogGapMeasure (show 0 < (sigma + tau) / 2 by linarith)
  apply ((hf.abs.mul_prod he).const_mul
    (pairedEtaHeatTransitionAmplitude h * pairedEtaHeatTransitionAmplitude k)⁻¹).mono'
  · exact hf.ofReal.aestronglyMeasurable.comp_fst.mul hm.aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hpos] with z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := mul_le_mul_of_nonneg_left
      (norm_pairedEtaOrderedGapReturnKernelCore_le hsigma hh htau hk hz.1 hz.2 phi psi z.2)
      (abs_nonneg (f z.1))
    simpa only [mul_left_comm] using hb

/-- Infinite intermediate-time integrability for both literal completed
current branches, with the physical head translation retained. -/
theorem integrable_leadingCurrent_gapReturn_prod (rho : NontrivialZetaZero) (N : ℕ)
    {sigma h tau k : ℝ} (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k)
    (hst : 0 < sigma + tau) {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z.1 : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi
        (z.1.1 + pairedEtaLogTailCutoff (N + 1)) z.1.2 z.2)
      (((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod
        pairedEtaLogGapMeasure) ∧
    Integrable (fun z : (ℝ × ℝ) × ℝ ↦
      (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z.1 : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi z.1.1 z.1.2 z.2)
      (((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod
        pairedEtaLogGapMeasure) := by
  constructor
  · apply integrable_current_gapReturn_prod (integrable_topPrefixFiniteEnergyHeadKernel rho N)
      (measurable_fst.add_const _) _ hsigma hh htau hk hst hphi hpsi
    filter_upwards [ae_pair_mem_pairedEtaLogSupport_headMeasure N] with p hp
    exact ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, (pairedEtaLogSupport_subset_Ioi_zero hp.2).le⟩
  · apply integrable_current_gapReturn_prod (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      measurable_fst _ hsigma hh htau hk hst hphi hpsi
    filter_upwards [ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2)] with p hp
    exact ⟨(pairedEtaLogSupport_subset_Ioi_zero hp.1).le, (pairedEtaLogSupport_subset_Ioi_zero hp.2).le⟩

/-- The full infinite-time return pairing of the original completed current. -/
def pairedEtaLeadingCurrentIntegratedGapReturn (rho : NontrivialZetaZero) (N : ℕ)
    (sigma h tau k : ℝ) (phi psi : ℝ → ℝ) : ℂ :=
  ∫ w, pairedEtaLeadingCurrentGapReturnPairing rho N sigma h tau k phi psi w
    ∂pairedEtaLogGapMeasure

/-- The intermediate-time integral defining the completed return converges
absolutely at positive total tilt. -/
theorem integrable_pairedEtaLeadingCurrentGapReturnPairing (rho : NontrivialZetaZero) (N : ℕ)
    {sigma h tau k : ℝ} (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k)
    (hst : 0 < sigma + tau) {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (pairedEtaLeadingCurrentGapReturnPairing rho N sigma h tau k phi psi)
      pairedEtaLogGapMeasure := by
  obtain ⟨hhead, hadj⟩ := integrable_leadingCurrent_gapReturn_prod rho N hsigma hh htau hk hst hphi hpsi
  unfold pairedEtaLeadingCurrentGapReturnPairing
  split
  · exact hhead.integral_prod_right
  · exact hadj.integral_prod_right

/-- Fubini identifies the full return with the literal three-time current
integral; no phase or multiplicity information is discarded. -/
theorem pairedEtaLeadingCurrentIntegratedGapReturn_eq_prod (rho : NontrivialZetaZero) (N : ℕ)
    {sigma h tau k : ℝ} (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k)
    (hst : 0 < sigma + tau) {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    pairedEtaLeadingCurrentIntegratedGapReturn rho N sigma h tau k phi psi =
      if analyticZetaZeroMultiplicity rho = 1 then
        ∫ z : (ℝ × ℝ) × ℝ, (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N z.1 : ℂ) *
          pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi
            (z.1.1 + pairedEtaLogTailCutoff (N + 1)) z.1.2 z.2
          ∂(((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod
            pairedEtaLogGapMeasure)
      else
        ∫ z : (ℝ × ℝ) × ℝ, (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z.1 : ℂ) *
          pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi z.1.1 z.1.2 z.2
          ∂(((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))).prod
            pairedEtaLogGapMeasure) := by
  obtain ⟨hhead, hadj⟩ := integrable_leadingCurrent_gapReturn_prod rho N hsigma hh htau hk hst hphi hpsi
  unfold pairedEtaLeadingCurrentIntegratedGapReturn pairedEtaLeadingCurrentGapReturnPairing
  split
  · exact (integral_prod_symm _ hhead).symm
  · exact (integral_prod_symm _ hadj).symm

/-- The negative two-transition identity survives integration over every
actual gap time, with absolute convergence proved on both sides. -/
theorem pairedEtaLeadingCurrentIntegratedTwoTransition_eq_neg_gapReturn
    (rho : NontrivialZetaZero) (N : ℕ) {sigma h tau k : ℝ}
    (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k)
    (hst : 0 < sigma + tau) {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (pairedEtaLeadingCurrentTwoTransitionPairing rho N sigma h tau k phi psi)
        pairedEtaLogGapMeasure ∧
      (∫ w, pairedEtaLeadingCurrentTwoTransitionPairing rho N sigma h tau k phi psi w
        ∂pairedEtaLogGapMeasure) =
        -pairedEtaLeadingCurrentIntegratedGapReturn rho N sigma h tau k phi psi := by
  have heq : pairedEtaLeadingCurrentTwoTransitionPairing rho N sigma h tau k phi psi =ᵐ[pairedEtaLogGapMeasure]
      fun w ↦ -pairedEtaLeadingCurrentGapReturnPairing rho N sigma h tau k phi psi w := by
    filter_upwards [ae_mem_pairedEtaLogGapSupport] with w hw
    exact pairedEtaLeadingCurrentTwoTransitionPairing_eq_neg_gapReturn rho N sigma h tau k phi psi hw.1
  refine ⟨(integrable_pairedEtaLeadingCurrentGapReturnPairing rho N hsigma hh htau hk hst hphi hpsi).neg.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_neg]
  rfl

end

end RiemannGaussian
